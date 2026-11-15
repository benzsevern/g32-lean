import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0217
import HodgeLean.Foundations.Program.G32PropFourSixPacked0218
import HodgeLean.Foundations.Program.G32PropFourSixPacked0220
import HodgeLean.Foundations.Program.G32PropFourSixPacked0221
import HodgeLean.Foundations.Program.G32PropFourSixPacked0225

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_056982 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056982 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061279 := by
  decide +kernel

theorem g32p_supplierForest_actual_056982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056982) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_056982
    g32p_supplierForest_actual_061279

def g32p_supplierForest_node_057061 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057061 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057061 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_130215 := by
  decide +kernel

theorem g32p_supplierForest_actual_057061 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057061) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_057061
    g32p_supplierForest_actual_130215

def g32p_supplierForest_node_057138 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057138 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057138 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053976 := by
  decide +kernel

theorem g32p_supplierForest_actual_057138 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057138) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_057138
    g32p_supplierForest_actual_053976

def g32p_supplierForest_node_057141 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057141 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057141 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_063325 := by
  decide +kernel

theorem g32p_supplierForest_actual_057141 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057141) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_057141
    g32p_supplierForest_actual_063325

def g32p_supplierForest_node_057159 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057159 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050151 := by
  decide +kernel

theorem g32p_supplierForest_actual_057159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057159) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_057159
    g32p_supplierForest_actual_050151

def g32p_supplierForest_node_057166 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057166 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068151 := by
  decide +kernel

theorem g32p_supplierForest_actual_057166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057166) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_057166
    g32p_supplierForest_actual_068151

def g32p_supplierForest_node_057169 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_057169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057169 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048208 := by
  decide +kernel

theorem g32p_supplierForest_actual_057169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057169) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_057169
    g32p_supplierForest_actual_048208

def g32p_supplierForest_node_057170 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057170 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057170 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069905 := by
  decide +kernel

theorem g32p_supplierForest_actual_057170 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057170) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_057170
    g32p_supplierForest_actual_069905

def g32p_supplierForest_node_057181 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_057181 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057181 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069722 := by
  decide +kernel

theorem g32p_supplierForest_actual_057181 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057181) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_057181
    g32p_supplierForest_actual_069722

def g32p_supplierForest_node_057193 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_057193 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057193 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_008984 := by
  decide +kernel

theorem g32p_supplierForest_actual_057193 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057193) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 1 g32p_supplierForest_edge_057193
    g32p_supplierForest_actual_008984

def g32p_supplierForest_node_057211 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057211 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057211 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067103 := by
  decide +kernel

theorem g32p_supplierForest_actual_057211 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057211) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_057211
    g32p_supplierForest_actual_067103

def g32p_supplierForest_node_057219 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057219 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068220 := by
  decide +kernel

theorem g32p_supplierForest_actual_057219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057219) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_057219
    g32p_supplierForest_actual_068220

def g32p_supplierForest_node_057248 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057248 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057248 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067906 := by
  decide +kernel

theorem g32p_supplierForest_actual_057248 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057248) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_057248
    g32p_supplierForest_actual_067906

def g32p_supplierForest_node_057251 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_057251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057251 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059479 := by
  decide +kernel

theorem g32p_supplierForest_actual_057251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057251) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_057251
    g32p_supplierForest_actual_059479

def g32p_supplierForest_node_057264 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057264 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057264 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056342 := by
  decide +kernel

theorem g32p_supplierForest_actual_057264 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057264) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_057264
    g32p_supplierForest_actual_056342

def g32p_supplierForest_node_057294 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057294 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_134994 := by
  decide +kernel

theorem g32p_supplierForest_actual_057294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057294) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_057294
    g32p_supplierForest_actual_134994

def g32p_supplierForest_node_057303 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057303 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054367 := by
  decide +kernel

theorem g32p_supplierForest_actual_057303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057303) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_057303
    g32p_supplierForest_actual_054367

def g32p_supplierForest_node_057310 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_057310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057310 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054378 := by
  decide +kernel

theorem g32p_supplierForest_actual_057310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057310) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_057310
    g32p_supplierForest_actual_054378

def g32p_supplierForest_node_057327 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057327 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068341 := by
  decide +kernel

theorem g32p_supplierForest_actual_057327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057327) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_057327
    g32p_supplierForest_actual_068341

def g32p_supplierForest_node_057329 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057329 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057329 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068343 := by
  decide +kernel

theorem g32p_supplierForest_actual_057329 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057329) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 0 g32p_supplierForest_edge_057329
    g32p_supplierForest_actual_068343

def g32p_supplierForest_node_057334 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057334 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057334 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_141114 := by
  decide +kernel

theorem g32p_supplierForest_actual_057334 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057334) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_057334
    g32p_supplierForest_actual_141114

def g32p_supplierForest_node_057336 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057336 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_141729 := by
  decide +kernel

theorem g32p_supplierForest_actual_057336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057336) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_057336
    g32p_supplierForest_actual_141729

def g32p_supplierForest_node_057362 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057362 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057362 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064478 := by
  decide +kernel

theorem g32p_supplierForest_actual_057362 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057362) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_057362
    g32p_supplierForest_actual_064478

def g32p_supplierForest_node_057369 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057369 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057369 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062204 := by
  decide +kernel

theorem g32p_supplierForest_actual_057369 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057369) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_057369
    g32p_supplierForest_actual_062204

def g32p_supplierForest_node_057375 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057375 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057375 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007529 := by
  decide +kernel

theorem g32p_supplierForest_actual_057375 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057375) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_057375
    g32p_supplierForest_actual_007529

def g32p_supplierForest_node_057401 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057401 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057401 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068441 := by
  decide +kernel

theorem g32p_supplierForest_actual_057401 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057401) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_057401
    g32p_supplierForest_actual_068441

def g32p_supplierForest_node_057403 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057403 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057403 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057261 := by
  decide +kernel

theorem g32p_supplierForest_actual_057403 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057403) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_057403
    g32p_supplierForest_actual_057261

def g32p_supplierForest_node_057460 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057460 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057460 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_045124 := by
  decide +kernel

theorem g32p_supplierForest_actual_057460 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057460) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_057460
    g32p_supplierForest_actual_045124

def g32p_supplierForest_node_057474 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_057474 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057474 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068522 := by
  decide +kernel

theorem g32p_supplierForest_actual_057474 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057474) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_057474
    g32p_supplierForest_actual_068522

def g32p_supplierForest_node_057525 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_057525 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057525 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_139718 := by
  decide +kernel

theorem g32p_supplierForest_actual_057525 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057525) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_057525
    g32p_supplierForest_actual_139718

def g32p_supplierForest_node_057545 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057545 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_128406 := by
  decide +kernel

theorem g32p_supplierForest_actual_057545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057545) ∧
        IsConj g (g32p_literalRepresentative 79) := by
  exact g32p_archive_step_lift _ _ 79 1 g32p_supplierForest_edge_057545
    g32p_supplierForest_actual_128406

def g32p_supplierForest_node_057559 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057559 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057559 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056326 := by
  decide +kernel

theorem g32p_supplierForest_actual_057559 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057559) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_057559
    g32p_supplierForest_actual_056326

def g32p_supplierForest_node_057584 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_057584 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057584 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063756 := by
  decide +kernel

theorem g32p_supplierForest_actual_057584 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057584) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_057584
    g32p_supplierForest_actual_063756

def g32p_supplierForest_node_057604 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057604 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057604 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056423 := by
  decide +kernel

theorem g32p_supplierForest_actual_057604 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057604) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_057604
    g32p_supplierForest_actual_056423

def g32p_supplierForest_node_057657 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057657 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057657 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064064 := by
  decide +kernel

theorem g32p_supplierForest_actual_057657 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057657) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_057657
    g32p_supplierForest_actual_064064

def g32p_supplierForest_node_057663 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057663 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057663 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_054596 := by
  decide +kernel

theorem g32p_supplierForest_actual_057663 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057663) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 1 g32p_supplierForest_edge_057663
    g32p_supplierForest_actual_054596

def g32p_supplierForest_node_057703 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_057703 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057703 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068781 := by
  decide +kernel

theorem g32p_supplierForest_actual_057703 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057703) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_057703
    g32p_supplierForest_actual_068781

def g32p_supplierForest_node_057732 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057732 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056729 := by
  decide +kernel

theorem g32p_supplierForest_actual_057732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057732) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_057732
    g32p_supplierForest_actual_056729

def g32p_supplierForest_node_057739 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057739 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057739 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_061813 := by
  decide +kernel

theorem g32p_supplierForest_actual_057739 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057739) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_057739
    g32p_supplierForest_actual_061813

def g32p_supplierForest_node_057753 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_057753 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057753 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068854 := by
  decide +kernel

theorem g32p_supplierForest_actual_057753 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057753) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 1 g32p_supplierForest_edge_057753
    g32p_supplierForest_actual_068854

def g32p_supplierForest_node_057768 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057768 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057768 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010631 := by
  decide +kernel

theorem g32p_supplierForest_actual_057768 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057768) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_057768
    g32p_supplierForest_actual_010631

def g32p_supplierForest_node_057790 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_057790 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057790 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_048110 := by
  decide +kernel

theorem g32p_supplierForest_actual_057790 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057790) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_057790
    g32p_supplierForest_actual_048110

def g32p_supplierForest_node_057805 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_057805 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057805 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012148 := by
  decide +kernel

theorem g32p_supplierForest_actual_057805 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057805) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_057805
    g32p_supplierForest_actual_012148

def g32p_supplierForest_node_057813 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_057813 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057813 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055694 := by
  decide +kernel

theorem g32p_supplierForest_actual_057813 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057813) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_057813
    g32p_supplierForest_actual_055694

def g32p_supplierForest_node_057819 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057819 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057819 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012253 := by
  decide +kernel

theorem g32p_supplierForest_actual_057819 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057819) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_057819
    g32p_supplierForest_actual_012253

def g32p_supplierForest_node_057828 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_057828 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057828 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_048184 := by
  decide +kernel

theorem g32p_supplierForest_actual_057828 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057828) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_057828
    g32p_supplierForest_actual_048184

def g32p_supplierForest_node_057835 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057835 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057835 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057852 := by
  decide +kernel

theorem g32p_supplierForest_actual_057835 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057835) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_057835
    g32p_supplierForest_actual_057852

def g32p_supplierForest_node_057836 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_057836 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057836 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_057729 := by
  decide +kernel

theorem g32p_supplierForest_actual_057836 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057836) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_057836
    g32p_supplierForest_actual_057729

def g32p_supplierForest_node_057840 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_057840 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057840 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011122 := by
  decide +kernel

theorem g32p_supplierForest_actual_057840 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057840) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_057840
    g32p_supplierForest_actual_011122

def g32p_supplierForest_node_057844 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_057844 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057844 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057686 := by
  decide +kernel

theorem g32p_supplierForest_actual_057844 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057844) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_057844
    g32p_supplierForest_actual_057686

def g32p_supplierForest_node_057875 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_057875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057875 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_137827 := by
  decide +kernel

theorem g32p_supplierForest_actual_057875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057875) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_057875
    g32p_supplierForest_actual_137827

def g32p_supplierForest_node_057899 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057899 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009350 := by
  decide +kernel

theorem g32p_supplierForest_actual_057899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057899) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_057899
    g32p_supplierForest_actual_009350

def g32p_supplierForest_node_057925 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057925 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057925 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_007844 := by
  decide +kernel

theorem g32p_supplierForest_actual_057925 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057925) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_057925
    g32p_supplierForest_actual_007844

def g32p_supplierForest_node_057937 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_057937 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057937 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057196 := by
  decide +kernel

theorem g32p_supplierForest_actual_057937 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057937) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_057937
    g32p_supplierForest_actual_057196

def g32p_supplierForest_node_057970 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057970 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057970 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057495 := by
  decide +kernel

theorem g32p_supplierForest_actual_057970 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057970) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_057970
    g32p_supplierForest_actual_057495

def g32p_supplierForest_node_057999 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057999 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057999 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_069076 := by
  decide +kernel

theorem g32p_supplierForest_actual_057999 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057999) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_057999
    g32p_supplierForest_actual_069076

def g32p_supplierForest_node_058016 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_058016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058016 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011190 := by
  decide +kernel

theorem g32p_supplierForest_actual_058016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058016) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_058016
    g32p_supplierForest_actual_011190

def g32p_supplierForest_node_058035 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_058035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058035 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057625 := by
  decide +kernel

theorem g32p_supplierForest_actual_058035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058035) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_058035
    g32p_supplierForest_actual_057625

def g32p_supplierForest_node_058079 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058079 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058079 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_069160 := by
  decide +kernel

theorem g32p_supplierForest_actual_058079 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058079) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_058079
    g32p_supplierForest_actual_069160

def g32p_supplierForest_node_058092 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_058092 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058092 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071495 := by
  decide +kernel

theorem g32p_supplierForest_actual_058092 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058092) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_058092
    g32p_supplierForest_actual_071495

def g32p_supplierForest_node_058167 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058167 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068164 := by
  decide +kernel

theorem g32p_supplierForest_actual_058167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058167) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_058167
    g32p_supplierForest_actual_068164

def g32p_supplierForest_node_058177 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_058177 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058177 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_069257 := by
  decide +kernel

theorem g32p_supplierForest_actual_058177 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058177) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_058177
    g32p_supplierForest_actual_069257

def g32p_supplierForest_node_058185 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_058185 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058185 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049327 := by
  decide +kernel

theorem g32p_supplierForest_actual_058185 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058185) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_058185
    g32p_supplierForest_actual_049327

def g32p_supplierForest_node_058188 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_058188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058188 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056713 := by
  decide +kernel

theorem g32p_supplierForest_actual_058188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058188) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_058188
    g32p_supplierForest_actual_056713

def g32p_supplierForest_node_058266 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_058266 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058266 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067973 := by
  decide +kernel

theorem g32p_supplierForest_actual_058266 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058266) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_058266
    g32p_supplierForest_actual_067973

def g32p_supplierForest_node_058387 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_058387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058387 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_056039 := by
  decide +kernel

theorem g32p_supplierForest_actual_058387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058387) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_058387
    g32p_supplierForest_actual_056039

def g32p_supplierForest_node_058424 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058424 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058424 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_057683 := by
  decide +kernel

theorem g32p_supplierForest_actual_058424 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058424) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_058424
    g32p_supplierForest_actual_057683

def g32p_supplierForest_node_058429 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_058429 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058429 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064861 := by
  decide +kernel

theorem g32p_supplierForest_actual_058429 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058429) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_058429
    g32p_supplierForest_actual_064861

def g32p_supplierForest_node_058430 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058430 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058430 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_059309 := by
  decide +kernel

theorem g32p_supplierForest_actual_058430 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058430) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_058430
    g32p_supplierForest_actual_059309

def g32p_supplierForest_node_058452 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_058452 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058452 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011389 := by
  decide +kernel

theorem g32p_supplierForest_actual_058452 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058452) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_058452
    g32p_supplierForest_actual_011389

def g32p_supplierForest_node_058494 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_058494 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058494 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_068611 := by
  decide +kernel

theorem g32p_supplierForest_actual_058494 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058494) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_058494
    g32p_supplierForest_actual_068611

def g32p_supplierForest_node_058601 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_058601 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058601 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046779 := by
  decide +kernel

theorem g32p_supplierForest_actual_058601 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058601) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_058601
    g32p_supplierForest_actual_046779

def g32p_supplierForest_node_058603 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_058603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058603 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067127 := by
  decide +kernel

theorem g32p_supplierForest_actual_058603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058603) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 3 g32p_supplierForest_edge_058603
    g32p_supplierForest_actual_067127

def g32p_supplierForest_node_058605 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_058605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058605 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_134623 := by
  decide +kernel

theorem g32p_supplierForest_actual_058605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058605) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_058605
    g32p_supplierForest_actual_134623

def g32p_supplierForest_node_058607 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_058607 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058607 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048039 := by
  decide +kernel

theorem g32p_supplierForest_actual_058607 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058607) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_058607
    g32p_supplierForest_actual_048039

def g32p_supplierForest_node_058633 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_058633 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058633 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_063756 := by
  decide +kernel

theorem g32p_supplierForest_actual_058633 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058633) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_058633
    g32p_supplierForest_actual_063756

def g32p_supplierForest_node_058690 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_058690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058690 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_069487 := by
  decide +kernel

theorem g32p_supplierForest_actual_058690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058690) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_058690
    g32p_supplierForest_actual_069487

def g32p_supplierForest_node_058831 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058831 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058831 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049608 := by
  decide +kernel

theorem g32p_supplierForest_actual_058831 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058831) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_058831
    g32p_supplierForest_actual_049608

def g32p_supplierForest_node_058882 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_058882 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058882 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049378 := by
  decide +kernel

theorem g32p_supplierForest_actual_058882 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058882) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_058882
    g32p_supplierForest_actual_049378

def g32p_supplierForest_node_058898 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_058898 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058898 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058235 := by
  decide +kernel

theorem g32p_supplierForest_actual_058898 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058898) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_058898
    g32p_supplierForest_actual_058235

def g32p_supplierForest_node_058945 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_058945 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058945 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135579 := by
  decide +kernel

theorem g32p_supplierForest_actual_058945 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058945) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_058945
    g32p_supplierForest_actual_135579

def g32p_supplierForest_node_058954 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_058954 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058954 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011607 := by
  decide +kernel

theorem g32p_supplierForest_actual_058954 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058954) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_058954
    g32p_supplierForest_actual_011607

def g32p_supplierForest_node_058972 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_058972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058972 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060431 := by
  decide +kernel

theorem g32p_supplierForest_actual_058972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058972) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_058972
    g32p_supplierForest_actual_060431

def g32p_supplierForest_node_058982 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_058982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058982 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060441 := by
  decide +kernel

theorem g32p_supplierForest_actual_058982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058982) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_058982
    g32p_supplierForest_actual_060441

def g32p_supplierForest_node_059001 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059001 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059001 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070096 := by
  decide +kernel

theorem g32p_supplierForest_actual_059001 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059001) ∧
        IsConj g (g32p_literalRepresentative 79) := by
  exact g32p_archive_step_lift _ _ 79 0 g32p_supplierForest_edge_059001
    g32p_supplierForest_actual_070096

def g32p_supplierForest_node_059042 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_059042 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059042 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_056876 := by
  decide +kernel

theorem g32p_supplierForest_actual_059042 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059042) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_059042
    g32p_supplierForest_actual_056876

def g32p_supplierForest_node_059062 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059062 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059062 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_012302 := by
  decide +kernel

theorem g32p_supplierForest_actual_059062 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059062) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_059062
    g32p_supplierForest_actual_012302

def g32p_supplierForest_node_059091 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059091 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058534 := by
  decide +kernel

theorem g32p_supplierForest_actual_059091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059091) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_059091
    g32p_supplierForest_actual_058534

def g32p_supplierForest_node_059167 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059167 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059551 := by
  decide +kernel

theorem g32p_supplierForest_actual_059167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059167) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 3 g32p_supplierForest_edge_059167
    g32p_supplierForest_actual_059551

def g32p_supplierForest_node_059196 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059196 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059196 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054109 := by
  decide +kernel

theorem g32p_supplierForest_actual_059196 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059196) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_059196
    g32p_supplierForest_actual_054109

def g32p_supplierForest_node_059216 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_059216 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059216 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006974 := by
  decide +kernel

theorem g32p_supplierForest_actual_059216 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059216) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_059216
    g32p_supplierForest_actual_006974

def g32p_supplierForest_node_059217 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_059217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059217 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045894 := by
  decide +kernel

theorem g32p_supplierForest_actual_059217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059217) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_059217
    g32p_supplierForest_actual_045894

def g32p_supplierForest_node_059256 : HurwitzPrymRex_Mat :=
  ![![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059256 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059256 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046481 := by
  decide +kernel

theorem g32p_supplierForest_actual_059256 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059256) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 3 g32p_supplierForest_edge_059256
    g32p_supplierForest_actual_046481

def g32p_supplierForest_node_059258 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059258 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059258 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070338 := by
  decide +kernel

theorem g32p_supplierForest_actual_059258 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059258) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_059258
    g32p_supplierForest_actual_070338

def g32p_supplierForest_node_059270 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059270 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_045286 := by
  decide +kernel

theorem g32p_supplierForest_actual_059270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059270) ∧
        IsConj g (g32p_literalRepresentative 67) := by
  exact g32p_archive_step_lift _ _ 67 0 g32p_supplierForest_edge_059270
    g32p_supplierForest_actual_045286

def g32p_supplierForest_node_059295 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_059295 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059295 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011752 := by
  decide +kernel

theorem g32p_supplierForest_actual_059295 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059295) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 0 g32p_supplierForest_edge_059295
    g32p_supplierForest_actual_011752

def g32p_supplierForest_node_059305 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_059305 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059305 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057284 := by
  decide +kernel

theorem g32p_supplierForest_actual_059305 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059305) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_059305
    g32p_supplierForest_actual_057284

def g32p_supplierForest_node_059336 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059336 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059336 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068449 := by
  decide +kernel

theorem g32p_supplierForest_actual_059336 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059336) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_059336
    g32p_supplierForest_actual_068449

def g32p_supplierForest_node_059419 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059419 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070467 := by
  decide +kernel

theorem g32p_supplierForest_actual_059419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059419) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_059419
    g32p_supplierForest_actual_070467

def g32p_supplierForest_node_059475 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_059475 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059475 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070578 := by
  decide +kernel

theorem g32p_supplierForest_actual_059475 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059475) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_059475
    g32p_supplierForest_actual_070578

def g32p_supplierForest_node_059486 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_059486 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059486 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053060 := by
  decide +kernel

theorem g32p_supplierForest_actual_059486 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059486) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_059486
    g32p_supplierForest_actual_053060

def g32p_supplierForest_node_059498 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059498 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059498 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_054170 := by
  decide +kernel

theorem g32p_supplierForest_actual_059498 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059498) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_059498
    g32p_supplierForest_actual_054170

def g32p_supplierForest_node_059509 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_059509 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059509 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062915 := by
  decide +kernel

theorem g32p_supplierForest_actual_059509 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059509) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_059509
    g32p_supplierForest_actual_062915

def g32p_supplierForest_node_059514 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_059514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059514 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006985 := by
  decide +kernel

theorem g32p_supplierForest_actual_059514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059514) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_059514
    g32p_supplierForest_actual_006985

def g32p_supplierForest_node_059518 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059518 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059518 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_053198 := by
  decide +kernel

theorem g32p_supplierForest_actual_059518 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059518) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_059518
    g32p_supplierForest_actual_053198

def g32p_supplierForest_node_059603 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059603 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059603 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010203 := by
  decide +kernel

theorem g32p_supplierForest_actual_059603 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059603) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_059603
    g32p_supplierForest_actual_010203

def g32p_supplierForest_node_059639 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059639 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059639 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_053628 := by
  decide +kernel

theorem g32p_supplierForest_actual_059639 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059639) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 0 g32p_supplierForest_edge_059639
    g32p_supplierForest_actual_053628

def g32p_supplierForest_node_059644 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059644 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059644 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070749 := by
  decide +kernel

theorem g32p_supplierForest_actual_059644 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059644) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_059644
    g32p_supplierForest_actual_070749

def g32p_supplierForest_node_059722 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059722 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056039 := by
  decide +kernel

theorem g32p_supplierForest_actual_059722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059722) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_059722
    g32p_supplierForest_actual_056039

def g32p_supplierForest_node_059733 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059733 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059733 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064484 := by
  decide +kernel

theorem g32p_supplierForest_actual_059733 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059733) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_059733
    g32p_supplierForest_actual_064484

def g32p_supplierForest_node_059734 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059734 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059734 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_069744 := by
  decide +kernel

theorem g32p_supplierForest_actual_059734 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059734) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_059734
    g32p_supplierForest_actual_069744

def g32p_supplierForest_node_059766 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059766 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059766 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070879 := by
  decide +kernel

theorem g32p_supplierForest_actual_059766 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059766) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_059766
    g32p_supplierForest_actual_070879

def g32p_supplierForest_node_059783 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_059783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059783 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_011949 := by
  decide +kernel

theorem g32p_supplierForest_actual_059783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059783) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_059783
    g32p_supplierForest_actual_011949

def g32p_supplierForest_node_059799 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_059799 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059799 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_129986 := by
  decide +kernel

theorem g32p_supplierForest_actual_059799 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059799) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_059799
    g32p_supplierForest_actual_129986

def g32p_supplierForest_node_059823 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059823 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059823 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_069722 := by
  decide +kernel

theorem g32p_supplierForest_actual_059823 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059823) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_059823
    g32p_supplierForest_actual_069722

def g32p_supplierForest_node_059824 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_059824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059824 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_128624 := by
  decide +kernel

theorem g32p_supplierForest_actual_059824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059824) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_059824
    g32p_supplierForest_actual_128624

def g32p_supplierForest_node_059830 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_059830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059830 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070961 := by
  decide +kernel

theorem g32p_supplierForest_actual_059830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059830) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_059830
    g32p_supplierForest_actual_070961

def g32p_supplierForest_node_059850 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_059850 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059850 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_011390 := by
  decide +kernel

theorem g32p_supplierForest_actual_059850 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059850) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_059850
    g32p_supplierForest_actual_011390

def g32p_supplierForest_node_059925 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_059925 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059925 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062424 := by
  decide +kernel

theorem g32p_supplierForest_actual_059925 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059925) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_059925
    g32p_supplierForest_actual_062424

def g32p_supplierForest_node_059928 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059928 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059928 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062309 := by
  decide +kernel

theorem g32p_supplierForest_actual_059928 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059928) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_059928
    g32p_supplierForest_actual_062309

def g32p_supplierForest_node_059939 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_059939 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059939 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044826 := by
  decide +kernel

theorem g32p_supplierForest_actual_059939 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059939) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 3 g32p_supplierForest_edge_059939
    g32p_supplierForest_actual_044826

def g32p_supplierForest_node_060016 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060016 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071157 := by
  decide +kernel

theorem g32p_supplierForest_actual_060016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060016) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_060016
    g32p_supplierForest_actual_071157

def g32p_supplierForest_node_060032 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_060032 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060032 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071494 := by
  decide +kernel

theorem g32p_supplierForest_actual_060032 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060032) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_060032
    g32p_supplierForest_actual_071494

def g32p_supplierForest_node_060057 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060057 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010233 := by
  decide +kernel

theorem g32p_supplierForest_actual_060057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060057) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_060057
    g32p_supplierForest_actual_010233

def g32p_supplierForest_node_060089 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_060089 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060089 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_050544 := by
  decide +kernel

theorem g32p_supplierForest_actual_060089 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060089) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_060089
    g32p_supplierForest_actual_050544

def g32p_supplierForest_node_060095 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_060095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060095 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_137683 := by
  decide +kernel

theorem g32p_supplierForest_actual_060095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060095) ∧
        IsConj g (g32p_literalRepresentative 77) := by
  exact g32p_archive_step_lift _ _ 77 1 g32p_supplierForest_edge_060095
    g32p_supplierForest_actual_137683

def g32p_supplierForest_node_060101 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060101 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060101 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069985 := by
  decide +kernel

theorem g32p_supplierForest_actual_060101 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060101) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_060101
    g32p_supplierForest_actual_069985

def g32p_supplierForest_node_060140 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060140 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060140 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067147 := by
  decide +kernel

theorem g32p_supplierForest_actual_060140 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060140) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_060140
    g32p_supplierForest_actual_067147

def g32p_supplierForest_node_060155 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_060155 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060155 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065872 := by
  decide +kernel

theorem g32p_supplierForest_actual_060155 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060155) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_060155
    g32p_supplierForest_actual_065872

def g32p_supplierForest_node_060165 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060165 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060165 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067162 := by
  decide +kernel

theorem g32p_supplierForest_actual_060165 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060165) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_060165
    g32p_supplierForest_actual_067162

def g32p_supplierForest_node_060202 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060202 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057393 := by
  decide +kernel

theorem g32p_supplierForest_actual_060202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060202) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_060202
    g32p_supplierForest_actual_057393

def g32p_supplierForest_node_060227 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060227 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069985 := by
  decide +kernel

theorem g32p_supplierForest_actual_060227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060227) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_060227
    g32p_supplierForest_actual_069985

def g32p_supplierForest_node_060253 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060253 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060253 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060167 := by
  decide +kernel

theorem g32p_supplierForest_actual_060253 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060253) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_060253
    g32p_supplierForest_actual_060167

def g32p_supplierForest_node_060257 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_060257 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060257 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057394 := by
  decide +kernel

theorem g32p_supplierForest_actual_060257 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060257) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_060257
    g32p_supplierForest_actual_057394

def g32p_supplierForest_node_060276 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060276 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060276 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057687 := by
  decide +kernel

theorem g32p_supplierForest_actual_060276 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060276) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_060276
    g32p_supplierForest_actual_057687

def g32p_supplierForest_node_060284 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060284 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_052965 := by
  decide +kernel

theorem g32p_supplierForest_actual_060284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060284) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_060284
    g32p_supplierForest_actual_052965

def g32p_supplierForest_node_060294 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_060294 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060294 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_012174 := by
  decide +kernel

theorem g32p_supplierForest_actual_060294 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060294) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 0 g32p_supplierForest_edge_060294
    g32p_supplierForest_actual_012174

def g32p_supplierForest_node_060348 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060348 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060348 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_139567 := by
  decide +kernel

theorem g32p_supplierForest_actual_060348 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060348) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_060348
    g32p_supplierForest_actual_139567

def g32p_supplierForest_node_060349 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060349 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060349 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062312 := by
  decide +kernel

theorem g32p_supplierForest_actual_060349 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060349) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_060349
    g32p_supplierForest_actual_062312

def g32p_supplierForest_node_060372 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_060372 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060372 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_127904 := by
  decide +kernel

theorem g32p_supplierForest_actual_060372 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060372) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_060372
    g32p_supplierForest_actual_127904

def g32p_supplierForest_node_060397 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060397 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060397 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_129691 := by
  decide +kernel

theorem g32p_supplierForest_actual_060397 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060397) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_060397
    g32p_supplierForest_actual_129691

def g32p_supplierForest_node_060455 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_060455 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060455 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046261 := by
  decide +kernel

theorem g32p_supplierForest_actual_060455 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060455) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_060455
    g32p_supplierForest_actual_046261

def g32p_supplierForest_node_060583 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060583 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060583 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_128889 := by
  decide +kernel

theorem g32p_supplierForest_actual_060583 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060583) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_060583
    g32p_supplierForest_actual_128889

def g32p_supplierForest_node_060611 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_060611 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060611 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008590 := by
  decide +kernel

theorem g32p_supplierForest_actual_060611 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060611) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_060611
    g32p_supplierForest_actual_008590

def g32p_supplierForest_node_060618 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060618 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008599 := by
  decide +kernel

theorem g32p_supplierForest_actual_060618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060618) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_060618
    g32p_supplierForest_actual_008599

def g32p_supplierForest_node_060637 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_060637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060637 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046790 := by
  decide +kernel

theorem g32p_supplierForest_actual_060637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060637) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_060637
    g32p_supplierForest_actual_046790

def g32p_supplierForest_node_060645 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_060645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060645 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_057098 := by
  decide +kernel

theorem g32p_supplierForest_actual_060645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060645) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_060645
    g32p_supplierForest_actual_057098

def g32p_supplierForest_node_060662 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_060662 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060662 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060636 := by
  decide +kernel

theorem g32p_supplierForest_actual_060662 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060662) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_060662
    g32p_supplierForest_actual_060636

def g32p_supplierForest_node_060675 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060675 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060675 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127883 := by
  decide +kernel

theorem g32p_supplierForest_actual_060675 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060675) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_060675
    g32p_supplierForest_actual_127883

def g32p_supplierForest_node_060711 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060711 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060711 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047070 := by
  decide +kernel

theorem g32p_supplierForest_actual_060711 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060711) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_060711
    g32p_supplierForest_actual_047070

def g32p_supplierForest_node_060735 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060735 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060735 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138149 := by
  decide +kernel

theorem g32p_supplierForest_actual_060735 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060735) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_060735
    g32p_supplierForest_actual_138149

def g32p_supplierForest_node_060738 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_060738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060738 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_127950 := by
  decide +kernel

theorem g32p_supplierForest_actual_060738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060738) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_060738
    g32p_supplierForest_actual_127950

def g32p_supplierForest_node_060740 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_060740 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060740 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_052632 := by
  decide +kernel

theorem g32p_supplierForest_actual_060740 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060740) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_060740
    g32p_supplierForest_actual_052632

def g32p_supplierForest_node_060745 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060745 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060745 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061830 := by
  decide +kernel

theorem g32p_supplierForest_actual_060745 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060745) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_060745
    g32p_supplierForest_actual_061830

def g32p_supplierForest_node_060800 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060800 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060800 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_044571 := by
  decide +kernel

theorem g32p_supplierForest_actual_060800 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060800) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_060800
    g32p_supplierForest_actual_044571

def g32p_supplierForest_node_060801 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060801 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050687 := by
  decide +kernel

theorem g32p_supplierForest_actual_060801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060801) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 2 g32p_supplierForest_edge_060801
    g32p_supplierForest_actual_050687

def g32p_supplierForest_node_060871 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060871 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060871 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047609 := by
  decide +kernel

theorem g32p_supplierForest_actual_060871 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060871) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_060871
    g32p_supplierForest_actual_047609

def g32p_supplierForest_node_060902 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_060902 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060902 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_009197 := by
  decide +kernel

theorem g32p_supplierForest_actual_060902 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060902) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_060902
    g32p_supplierForest_actual_009197

def g32p_supplierForest_node_060929 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060929 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060929 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_129469 := by
  decide +kernel

theorem g32p_supplierForest_actual_060929 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060929) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_060929
    g32p_supplierForest_actual_129469

def g32p_supplierForest_node_060944 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_060944 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060944 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047923 := by
  decide +kernel

theorem g32p_supplierForest_actual_060944 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060944) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_060944
    g32p_supplierForest_actual_047923

def g32p_supplierForest_node_060980 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060980 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051811 := by
  decide +kernel

theorem g32p_supplierForest_actual_060980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060980) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_060980
    g32p_supplierForest_actual_051811

def g32p_supplierForest_node_060999 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060999 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060999 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128233 := by
  decide +kernel

theorem g32p_supplierForest_actual_060999 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060999) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_060999
    g32p_supplierForest_actual_128233

def g32p_supplierForest_node_061017 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061017 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058704 := by
  decide +kernel

theorem g32p_supplierForest_actual_061017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061017) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_061017
    g32p_supplierForest_actual_058704

def g32p_supplierForest_node_061024 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061024 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061024 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_045477 := by
  decide +kernel

theorem g32p_supplierForest_actual_061024 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061024) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_061024
    g32p_supplierForest_actual_045477

def g32p_supplierForest_node_061043 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061043 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061043 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046756 := by
  decide +kernel

theorem g32p_supplierForest_actual_061043 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061043) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 1 g32p_supplierForest_edge_061043
    g32p_supplierForest_actual_046756

def g32p_supplierForest_node_061081 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061081 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061081 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128313 := by
  decide +kernel

theorem g32p_supplierForest_actual_061081 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061081) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_061081
    g32p_supplierForest_actual_128313

def g32p_supplierForest_node_061088 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061088 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061088 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_057128 := by
  decide +kernel

theorem g32p_supplierForest_actual_061088 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061088) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_061088
    g32p_supplierForest_actual_057128

def g32p_supplierForest_node_061103 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061103 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130409 := by
  decide +kernel

theorem g32p_supplierForest_actual_061103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061103) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_061103
    g32p_supplierForest_actual_130409

def g32p_supplierForest_node_061149 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061149 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061149 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_006309 := by
  decide +kernel

theorem g32p_supplierForest_actual_061149 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061149) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_061149
    g32p_supplierForest_actual_006309

def g32p_supplierForest_node_061169 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061169 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061169 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047727 := by
  decide +kernel

theorem g32p_supplierForest_actual_061169 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061169) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_061169
    g32p_supplierForest_actual_047727

def g32p_supplierForest_node_061194 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061194 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065079 := by
  decide +kernel

theorem g32p_supplierForest_actual_061194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061194) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_061194
    g32p_supplierForest_actual_065079

def g32p_supplierForest_node_061231 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061231 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047022 := by
  decide +kernel

theorem g32p_supplierForest_actual_061231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061231) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_061231
    g32p_supplierForest_actual_047022

def g32p_supplierForest_node_061251 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061251 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061251 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061097 := by
  decide +kernel

theorem g32p_supplierForest_actual_061251 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061251) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_061251
    g32p_supplierForest_actual_061097

def g32p_supplierForest_node_061289 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061289 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061289 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128545 := by
  decide +kernel

theorem g32p_supplierForest_actual_061289 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061289) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_061289
    g32p_supplierForest_actual_128545

def g32p_supplierForest_node_061310 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061310 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049060 := by
  decide +kernel

theorem g32p_supplierForest_actual_061310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061310) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 1 g32p_supplierForest_edge_061310
    g32p_supplierForest_actual_049060

def g32p_supplierForest_node_061360 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061360 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049573 := by
  decide +kernel

theorem g32p_supplierForest_actual_061360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061360) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_061360
    g32p_supplierForest_actual_049573

def g32p_supplierForest_node_061387 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061387 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061387 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063852 := by
  decide +kernel

theorem g32p_supplierForest_actual_061387 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061387) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_061387
    g32p_supplierForest_actual_063852

def g32p_supplierForest_node_061401 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061401 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061401 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_066132 := by
  decide +kernel

theorem g32p_supplierForest_actual_061401 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061401) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_061401
    g32p_supplierForest_actual_066132

def g32p_supplierForest_node_061444 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061444 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061444 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_046625 := by
  decide +kernel

theorem g32p_supplierForest_actual_061444 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061444) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_061444
    g32p_supplierForest_actual_046625

def g32p_supplierForest_node_061521 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061521 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061521 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065658 := by
  decide +kernel

theorem g32p_supplierForest_actual_061521 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061521) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_061521
    g32p_supplierForest_actual_065658

def g32p_supplierForest_node_061523 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061523 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061523 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051337 := by
  decide +kernel

theorem g32p_supplierForest_actual_061523 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061523) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_061523
    g32p_supplierForest_actual_051337

def g32p_supplierForest_node_061529 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061529 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006732 := by
  decide +kernel

theorem g32p_supplierForest_actual_061529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061529) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_061529
    g32p_supplierForest_actual_006732

def g32p_supplierForest_node_061531 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061531 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_056364 := by
  decide +kernel

theorem g32p_supplierForest_actual_061531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061531) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 0 g32p_supplierForest_edge_061531
    g32p_supplierForest_actual_056364

def g32p_supplierForest_node_061534 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061534 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131110 := by
  decide +kernel

theorem g32p_supplierForest_actual_061534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061534) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_061534
    g32p_supplierForest_actual_131110

def g32p_supplierForest_node_061539 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061539 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061539 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061604 := by
  decide +kernel

theorem g32p_supplierForest_actual_061539 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061539) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_061539
    g32p_supplierForest_actual_061604

def g32p_supplierForest_node_061543 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061543 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061543 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010684 := by
  decide +kernel

theorem g32p_supplierForest_actual_061543 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061543) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_061543
    g32p_supplierForest_actual_010684

def g32p_supplierForest_node_061548 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061548 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061548 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051635 := by
  decide +kernel

theorem g32p_supplierForest_actual_061548 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061548) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_061548
    g32p_supplierForest_actual_051635

def g32p_supplierForest_node_061550 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061550 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061550 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_059218 := by
  decide +kernel

theorem g32p_supplierForest_actual_061550 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061550) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_061550
    g32p_supplierForest_actual_059218

def g32p_supplierForest_node_061566 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061566 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047618 := by
  decide +kernel

theorem g32p_supplierForest_actual_061566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061566) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_061566
    g32p_supplierForest_actual_047618

def g32p_supplierForest_node_061606 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061606 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_061604 := by
  decide +kernel

theorem g32p_supplierForest_actual_061606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061606) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_061606
    g32p_supplierForest_actual_061604

def g32p_supplierForest_node_061625 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061625 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061625 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130215 := by
  decide +kernel

theorem g32p_supplierForest_actual_061625 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061625) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_061625
    g32p_supplierForest_actual_130215

def g32p_supplierForest_node_061632 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061632 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068781 := by
  decide +kernel

theorem g32p_supplierForest_actual_061632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061632) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_061632
    g32p_supplierForest_actual_068781

def g32p_supplierForest_node_061764 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061764 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061764 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064015 := by
  decide +kernel

theorem g32p_supplierForest_actual_061764 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061764) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_061764
    g32p_supplierForest_actual_064015

def g32p_supplierForest_node_061771 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061771 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061771 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_046755 := by
  decide +kernel

theorem g32p_supplierForest_actual_061771 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061771) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_061771
    g32p_supplierForest_actual_046755

def g32p_supplierForest_node_061782 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061782 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_044604 := by
  decide +kernel

theorem g32p_supplierForest_actual_061782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061782) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 3 g32p_supplierForest_edge_061782
    g32p_supplierForest_actual_044604

def g32p_supplierForest_node_061783 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061783 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061783 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065212 := by
  decide +kernel

theorem g32p_supplierForest_actual_061783 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061783) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_061783
    g32p_supplierForest_actual_065212

def g32p_supplierForest_node_061789 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_061789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061789 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_061929 := by
  decide +kernel

theorem g32p_supplierForest_actual_061789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061789) ∧
        IsConj g (g32p_literalRepresentative 79) := by
  exact g32p_archive_step_lift _ _ 79 0 g32p_supplierForest_edge_061789
    g32p_supplierForest_actual_061929

def g32p_supplierForest_node_061804 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061804 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061804 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056998 := by
  decide +kernel

theorem g32p_supplierForest_actual_061804 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061804) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_061804
    g32p_supplierForest_actual_056998

def g32p_supplierForest_node_061852 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061852 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061852 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_052028 := by
  decide +kernel

theorem g32p_supplierForest_actual_061852 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061852) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_061852
    g32p_supplierForest_actual_052028

def g32p_supplierForest_node_061854 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061854 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069094 := by
  decide +kernel

theorem g32p_supplierForest_actual_061854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061854) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_061854
    g32p_supplierForest_actual_069094

def g32p_supplierForest_node_061855 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061855 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068580 := by
  decide +kernel

theorem g32p_supplierForest_actual_061855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061855) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_061855
    g32p_supplierForest_actual_068580

def g32p_supplierForest_node_061899 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061899 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061899 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057244 := by
  decide +kernel

theorem g32p_supplierForest_actual_061899 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061899) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_061899
    g32p_supplierForest_actual_057244

def g32p_supplierForest_node_061900 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061900 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131333 := by
  decide +kernel

theorem g32p_supplierForest_actual_061900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061900) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_061900
    g32p_supplierForest_actual_131333

def g32p_supplierForest_node_061903 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061903 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061903 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_057284 := by
  decide +kernel

theorem g32p_supplierForest_actual_061903 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061903) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_061903
    g32p_supplierForest_actual_057284

def g32p_supplierForest_node_061941 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061941 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061941 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067040 := by
  decide +kernel

theorem g32p_supplierForest_actual_061941 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061941) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_061941
    g32p_supplierForest_actual_067040

def g32p_supplierForest_node_061947 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061947 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061947 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064115 := by
  decide +kernel

theorem g32p_supplierForest_actual_061947 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061947) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_061947
    g32p_supplierForest_actual_064115

def g32p_supplierForest_node_061991 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061991 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_007946 := by
  decide +kernel

theorem g32p_supplierForest_actual_061991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061991) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_061991
    g32p_supplierForest_actual_007946

def g32p_supplierForest_node_061993 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_061993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061993 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051983 := by
  decide +kernel

theorem g32p_supplierForest_actual_061993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061993) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_061993
    g32p_supplierForest_actual_051983

def g32p_supplierForest_node_062019 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062019 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062019 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_057394 := by
  decide +kernel

theorem g32p_supplierForest_actual_062019 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062019) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_062019
    g32p_supplierForest_actual_057394

def g32p_supplierForest_node_062031 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_062031 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062031 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056125 := by
  decide +kernel

theorem g32p_supplierForest_actual_062031 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062031) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_062031
    g32p_supplierForest_actual_056125

def g32p_supplierForest_node_062068 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_062068 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062068 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062549 := by
  decide +kernel

theorem g32p_supplierForest_actual_062068 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062068) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 3 g32p_supplierForest_edge_062068
    g32p_supplierForest_actual_062549

def g32p_supplierForest_node_062095 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062095 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_135708 := by
  decide +kernel

theorem g32p_supplierForest_actual_062095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062095) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_062095
    g32p_supplierForest_actual_135708

def g32p_supplierForest_node_062152 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_062152 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062152 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071413 := by
  decide +kernel

theorem g32p_supplierForest_actual_062152 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062152) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 0 g32p_supplierForest_edge_062152
    g32p_supplierForest_actual_071413

def g32p_supplierForest_node_062187 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062187 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062187 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058212 := by
  decide +kernel

theorem g32p_supplierForest_actual_062187 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062187) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_062187
    g32p_supplierForest_actual_058212

def g32p_supplierForest_node_062203 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062203 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062203 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055936 := by
  decide +kernel

theorem g32p_supplierForest_actual_062203 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062203) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_062203
    g32p_supplierForest_actual_055936

def g32p_supplierForest_node_062219 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062219 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046753 := by
  decide +kernel

theorem g32p_supplierForest_actual_062219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062219) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_062219
    g32p_supplierForest_actual_046753

def g32p_supplierForest_node_062224 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062224 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062224 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_140869 := by
  decide +kernel

theorem g32p_supplierForest_actual_062224 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062224) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_062224
    g32p_supplierForest_actual_140869

def g32p_supplierForest_node_062280 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062280 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062280 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063169 := by
  decide +kernel

theorem g32p_supplierForest_actual_062280 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062280) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_062280
    g32p_supplierForest_actual_063169

def g32p_supplierForest_node_062290 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062290 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058704 := by
  decide +kernel

theorem g32p_supplierForest_actual_062290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062290) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_062290
    g32p_supplierForest_actual_058704

def g32p_supplierForest_node_062301 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062301 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062301 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067026 := by
  decide +kernel

theorem g32p_supplierForest_actual_062301 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062301) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_062301
    g32p_supplierForest_actual_067026

def g32p_supplierForest_node_062317 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062317 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062317 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058810 := by
  decide +kernel

theorem g32p_supplierForest_actual_062317 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062317) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_062317
    g32p_supplierForest_actual_058810

def g32p_supplierForest_node_062324 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062324 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062324 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063411 := by
  decide +kernel

theorem g32p_supplierForest_actual_062324 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062324) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 0 g32p_supplierForest_edge_062324
    g32p_supplierForest_actual_063411

def g32p_supplierForest_node_062337 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062337 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062337 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_133171 := by
  decide +kernel

theorem g32p_supplierForest_actual_062337 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062337) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_062337
    g32p_supplierForest_actual_133171

def g32p_supplierForest_node_062338 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062338 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129528 := by
  decide +kernel

theorem g32p_supplierForest_actual_062338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062338) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_062338
    g32p_supplierForest_actual_129528

def g32p_supplierForest_node_062340 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_062340 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062340 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129530 := by
  decide +kernel

theorem g32p_supplierForest_actual_062340 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062340) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_062340
    g32p_supplierForest_actual_129530

def g32p_supplierForest_node_062374 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062374 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062374 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134623 := by
  decide +kernel

theorem g32p_supplierForest_actual_062374 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062374) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_062374
    g32p_supplierForest_actual_134623

def g32p_supplierForest_node_062400 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_062400 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062400 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129602 := by
  decide +kernel

theorem g32p_supplierForest_actual_062400 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062400) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_062400
    g32p_supplierForest_actual_129602

def g32p_supplierForest_node_062463 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062463 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062463 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129656 := by
  decide +kernel

theorem g32p_supplierForest_actual_062463 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062463) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_062463
    g32p_supplierForest_actual_129656

def g32p_supplierForest_node_062495 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062495 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062495 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059319 := by
  decide +kernel

theorem g32p_supplierForest_actual_062495 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062495) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_062495
    g32p_supplierForest_actual_059319

def g32p_supplierForest_node_062501 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062501 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062501 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065924 := by
  decide +kernel

theorem g32p_supplierForest_actual_062501 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062501) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_062501
    g32p_supplierForest_actual_065924

def g32p_supplierForest_node_062556 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062556 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062556 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059572 := by
  decide +kernel

theorem g32p_supplierForest_actual_062556 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062556) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 1 g32p_supplierForest_edge_062556
    g32p_supplierForest_actual_059572

def g32p_supplierForest_node_062575 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_062575 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062575 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066950 := by
  decide +kernel

theorem g32p_supplierForest_actual_062575 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062575) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_062575
    g32p_supplierForest_actual_066950

def g32p_supplierForest_node_062635 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_062635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062635 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062763 := by
  decide +kernel

theorem g32p_supplierForest_actual_062635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062635) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_062635
    g32p_supplierForest_actual_062763

def g32p_supplierForest_node_062659 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_062659 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062659 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059814 := by
  decide +kernel

theorem g32p_supplierForest_actual_062659 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062659) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_062659
    g32p_supplierForest_actual_059814

def g32p_supplierForest_node_062792 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062792 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062792 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_141856 := by
  decide +kernel

theorem g32p_supplierForest_actual_062792 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062792) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_062792
    g32p_supplierForest_actual_141856

def g32p_supplierForest_node_062797 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062797 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062797 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_065627 := by
  decide +kernel

theorem g32p_supplierForest_actual_062797 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062797) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_062797
    g32p_supplierForest_actual_065627

def g32p_supplierForest_node_062856 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_062856 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062856 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_009397 := by
  decide +kernel

theorem g32p_supplierForest_actual_062856 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062856) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_062856
    g32p_supplierForest_actual_009397

def g32p_supplierForest_node_062868 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062868 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_142843 := by
  decide +kernel

theorem g32p_supplierForest_actual_062868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062868) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 2 g32p_supplierForest_edge_062868
    g32p_supplierForest_actual_142843

def g32p_supplierForest_node_062901 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_062901 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062901 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_054345 := by
  decide +kernel

theorem g32p_supplierForest_actual_062901 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062901) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_062901
    g32p_supplierForest_actual_054345

def g32p_supplierForest_node_062917 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_062917 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062917 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_128624 := by
  decide +kernel

theorem g32p_supplierForest_actual_062917 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062917) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_062917
    g32p_supplierForest_actual_128624

def g32p_supplierForest_node_062955 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_062955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062955 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060451 := by
  decide +kernel

theorem g32p_supplierForest_actual_062955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062955) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_062955
    g32p_supplierForest_actual_060451

def g32p_supplierForest_node_062991 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_062991 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062991 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047783 := by
  decide +kernel

theorem g32p_supplierForest_actual_062991 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062991) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_062991
    g32p_supplierForest_actual_047783

def g32p_supplierForest_node_063007 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063007 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063007 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_128889 := by
  decide +kernel

theorem g32p_supplierForest_actual_063007 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063007) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 3 g32p_supplierForest_edge_063007
    g32p_supplierForest_actual_128889

def g32p_supplierForest_node_063057 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063057 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061065 := by
  decide +kernel

theorem g32p_supplierForest_actual_063057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063057) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_063057
    g32p_supplierForest_actual_061065

def g32p_supplierForest_node_063059 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063059 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009483 := by
  decide +kernel

theorem g32p_supplierForest_actual_063059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063059) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_063059
    g32p_supplierForest_actual_009483

def g32p_supplierForest_node_063078 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063078 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063078 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130258 := by
  decide +kernel

theorem g32p_supplierForest_actual_063078 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063078) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_063078
    g32p_supplierForest_actual_130258

def g32p_supplierForest_node_063104 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063104 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063104 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063097 := by
  decide +kernel

theorem g32p_supplierForest_actual_063104 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063104) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 2 g32p_supplierForest_edge_063104
    g32p_supplierForest_actual_063097

def g32p_supplierForest_node_063113 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063113 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063113 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134596 := by
  decide +kernel

theorem g32p_supplierForest_actual_063113 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063113) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_063113
    g32p_supplierForest_actual_134596

def g32p_supplierForest_node_063128 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063128 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063128 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061378 := by
  decide +kernel

theorem g32p_supplierForest_actual_063128 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063128) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_063128
    g32p_supplierForest_actual_061378

def g32p_supplierForest_node_063133 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063133 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063133 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_046973 := by
  decide +kernel

theorem g32p_supplierForest_actual_063133 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063133) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_063133
    g32p_supplierForest_actual_046973

def g32p_supplierForest_node_063154 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063154 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063154 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_055214 := by
  decide +kernel

theorem g32p_supplierForest_actual_063154 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063154) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063154
    g32p_supplierForest_actual_055214

def g32p_supplierForest_node_063168 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063168 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063168 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130335 := by
  decide +kernel

theorem g32p_supplierForest_actual_063168 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063168) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_063168
    g32p_supplierForest_actual_130335

def g32p_supplierForest_node_063197 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063197 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061404 := by
  decide +kernel

theorem g32p_supplierForest_actual_063197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063197) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_063197
    g32p_supplierForest_actual_061404

def g32p_supplierForest_node_063206 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063206 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063206 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049375 := by
  decide +kernel

theorem g32p_supplierForest_actual_063206 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063206) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_063206
    g32p_supplierForest_actual_049375

def g32p_supplierForest_node_063214 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063214 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063214 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_050703 := by
  decide +kernel

theorem g32p_supplierForest_actual_063214 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063214) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_063214
    g32p_supplierForest_actual_050703

def g32p_supplierForest_node_063222 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063222 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063222 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010055 := by
  decide +kernel

theorem g32p_supplierForest_actual_063222 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063222) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 3 g32p_supplierForest_edge_063222
    g32p_supplierForest_actual_010055

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_063224 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063224 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063224 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050687 := by
  decide +kernel

theorem g32p_supplierForest_actual_063224 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063224) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 1 g32p_supplierForest_edge_063224
    g32p_supplierForest_actual_050687

def g32p_supplierForest_node_063266 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063266 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063266 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130409 := by
  decide +kernel

theorem g32p_supplierForest_actual_063266 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063266) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 0 g32p_supplierForest_edge_063266
    g32p_supplierForest_actual_130409

def g32p_supplierForest_node_063272 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063272 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063272 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060812 := by
  decide +kernel

theorem g32p_supplierForest_actual_063272 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063272) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_063272
    g32p_supplierForest_actual_060812

def g32p_supplierForest_node_063273 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063273 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130412 := by
  decide +kernel

theorem g32p_supplierForest_actual_063273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063273) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_063273
    g32p_supplierForest_actual_130412

def g32p_supplierForest_node_063293 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063293 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063293 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130419 := by
  decide +kernel

theorem g32p_supplierForest_actual_063293 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063293) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_063293
    g32p_supplierForest_actual_130419

def g32p_supplierForest_node_063307 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063307 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063307 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063306 := by
  decide +kernel

theorem g32p_supplierForest_actual_063307 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063307) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_063307
    g32p_supplierForest_actual_063306

def g32p_supplierForest_node_063310 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063310 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063310 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046061 := by
  decide +kernel

theorem g32p_supplierForest_actual_063310 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063310) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_063310
    g32p_supplierForest_actual_046061

def g32p_supplierForest_node_063333 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063333 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063333 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061875 := by
  decide +kernel

theorem g32p_supplierForest_actual_063333 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063333) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_063333
    g32p_supplierForest_actual_061875

def g32p_supplierForest_node_063356 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063356 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063356 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070150 := by
  decide +kernel

theorem g32p_supplierForest_actual_063356 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063356) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_063356
    g32p_supplierForest_actual_070150

def g32p_supplierForest_node_063417 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063417 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063417 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049581 := by
  decide +kernel

theorem g32p_supplierForest_actual_063417 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063417) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 2 g32p_supplierForest_edge_063417
    g32p_supplierForest_actual_049581

def g32p_supplierForest_node_063440 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063440 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_063730 := by
  decide +kernel

theorem g32p_supplierForest_actual_063440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063440) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063440
    g32p_supplierForest_actual_063730

def g32p_supplierForest_node_063481 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_063481 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063481 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064314 := by
  decide +kernel

theorem g32p_supplierForest_actual_063481 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063481) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_063481
    g32p_supplierForest_actual_064314

def g32p_supplierForest_node_063482 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063482 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063482 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_139410 := by
  decide +kernel

theorem g32p_supplierForest_actual_063482 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063482) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_063482
    g32p_supplierForest_actual_139410

def g32p_supplierForest_node_063484 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063484 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063484 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045195 := by
  decide +kernel

theorem g32p_supplierForest_actual_063484 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063484) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_063484
    g32p_supplierForest_actual_045195

def g32p_supplierForest_node_063495 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063495 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063495 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_141042 := by
  decide +kernel

theorem g32p_supplierForest_actual_063495 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063495) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_063495
    g32p_supplierForest_actual_141042

def g32p_supplierForest_node_063502 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063502 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063502 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_054365 := by
  decide +kernel

theorem g32p_supplierForest_actual_063502 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063502) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 2 g32p_supplierForest_edge_063502
    g32p_supplierForest_actual_054365

def g32p_supplierForest_node_063510 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063510 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063510 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_045971 := by
  decide +kernel

theorem g32p_supplierForest_actual_063510 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063510) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_063510
    g32p_supplierForest_actual_045971

def g32p_supplierForest_node_063513 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063513 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063513 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_056556 := by
  decide +kernel

theorem g32p_supplierForest_actual_063513 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063513) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_063513
    g32p_supplierForest_actual_056556

def g32p_supplierForest_node_063527 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063527 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063527 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062426 := by
  decide +kernel

theorem g32p_supplierForest_actual_063527 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063527) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_063527
    g32p_supplierForest_actual_062426

def g32p_supplierForest_node_063566 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063566 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129981 := by
  decide +kernel

theorem g32p_supplierForest_actual_063566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063566) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_063566
    g32p_supplierForest_actual_129981

def g32p_supplierForest_node_063589 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063589 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063589 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051430 := by
  decide +kernel

theorem g32p_supplierForest_actual_063589 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063589) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_063589
    g32p_supplierForest_actual_051430

def g32p_supplierForest_node_063605 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063605 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061589 := by
  decide +kernel

theorem g32p_supplierForest_actual_063605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063605) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 1 g32p_supplierForest_edge_063605
    g32p_supplierForest_actual_061589

def g32p_supplierForest_node_063629 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063629 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063629 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062240 := by
  decide +kernel

theorem g32p_supplierForest_actual_063629 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063629) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_063629
    g32p_supplierForest_actual_062240

def g32p_supplierForest_node_063655 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063655 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063655 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_066471 := by
  decide +kernel

theorem g32p_supplierForest_actual_063655 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063655) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_063655
    g32p_supplierForest_actual_066471

def g32p_supplierForest_node_063671 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063671 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063671 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048346 := by
  decide +kernel

theorem g32p_supplierForest_actual_063671 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063671) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_063671
    g32p_supplierForest_actual_048346

def g32p_supplierForest_node_063674 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_063674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063674 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063540 := by
  decide +kernel

theorem g32p_supplierForest_actual_063674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063674) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_063674
    g32p_supplierForest_actual_063540

def g32p_supplierForest_node_063676 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063676 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063676 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_045341 := by
  decide +kernel

theorem g32p_supplierForest_actual_063676 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063676) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_063676
    g32p_supplierForest_actual_045341

def g32p_supplierForest_node_063688 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063688 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063688 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010792 := by
  decide +kernel

theorem g32p_supplierForest_actual_063688 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063688) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 3 g32p_supplierForest_edge_063688
    g32p_supplierForest_actual_010792

def g32p_supplierForest_node_063693 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063693 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063693 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071306 := by
  decide +kernel

theorem g32p_supplierForest_actual_063693 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063693) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_063693
    g32p_supplierForest_actual_071306

def g32p_supplierForest_node_063722 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_063722 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063722 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129471 := by
  decide +kernel

theorem g32p_supplierForest_actual_063722 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063722) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_063722
    g32p_supplierForest_actual_129471

def g32p_supplierForest_node_063729 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_063729 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063729 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070602 := by
  decide +kernel

theorem g32p_supplierForest_actual_063729 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063729) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_063729
    g32p_supplierForest_actual_070602

def g32p_supplierForest_node_063900 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_063900 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063900 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061589 := by
  decide +kernel

theorem g32p_supplierForest_actual_063900 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063900) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_063900
    g32p_supplierForest_actual_061589

def g32p_supplierForest_node_063920 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_063920 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063920 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064418 := by
  decide +kernel

theorem g32p_supplierForest_actual_063920 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063920) ∧
        IsConj g (g32p_literalRepresentative 5) := by
  exact g32p_archive_step_lift _ _ 5 2 g32p_supplierForest_edge_063920
    g32p_supplierForest_actual_064418

def g32p_supplierForest_node_064028 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064028 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064028 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059983 := by
  decide +kernel

theorem g32p_supplierForest_actual_064028 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064028) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 1 g32p_supplierForest_edge_064028
    g32p_supplierForest_actual_059983

def g32p_supplierForest_node_064041 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064041 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064041 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071623 := by
  decide +kernel

theorem g32p_supplierForest_actual_064041 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064041) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_064041
    g32p_supplierForest_actual_071623

def g32p_supplierForest_node_064045 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064045 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064045 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005906 := by
  decide +kernel

theorem g32p_supplierForest_actual_064045 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064045) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_064045
    g32p_supplierForest_actual_005906

def g32p_supplierForest_node_064056 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064056 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064056 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131110 := by
  decide +kernel

theorem g32p_supplierForest_actual_064056 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064056) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064056
    g32p_supplierForest_actual_131110

def g32p_supplierForest_node_064075 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064075 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064075 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064115 := by
  decide +kernel

theorem g32p_supplierForest_actual_064075 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064075) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064075
    g32p_supplierForest_actual_064115

def g32p_supplierForest_node_064183 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064183 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064183 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_143543 := by
  decide +kernel

theorem g32p_supplierForest_actual_064183 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064183) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_064183
    g32p_supplierForest_actual_143543

def g32p_supplierForest_node_064202 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064202 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130987 := by
  decide +kernel

theorem g32p_supplierForest_actual_064202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064202) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_064202
    g32p_supplierForest_actual_130987

def g32p_supplierForest_node_064205 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064205 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064205 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062872 := by
  decide +kernel

theorem g32p_supplierForest_actual_064205 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064205) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_064205
    g32p_supplierForest_actual_062872

def g32p_supplierForest_node_064207 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064207 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064207 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067246 := by
  decide +kernel

theorem g32p_supplierForest_actual_064207 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064207) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_064207
    g32p_supplierForest_actual_067246

def g32p_supplierForest_node_064270 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064270 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010815 := by
  decide +kernel

theorem g32p_supplierForest_actual_064270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064270) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_064270
    g32p_supplierForest_actual_010815

def g32p_supplierForest_node_064287 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064287 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064287 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_134947 := by
  decide +kernel

theorem g32p_supplierForest_actual_064287 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064287) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_064287
    g32p_supplierForest_actual_134947

def g32p_supplierForest_node_064355 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064355 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064355 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071191 := by
  decide +kernel

theorem g32p_supplierForest_actual_064355 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064355) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_064355
    g32p_supplierForest_actual_071191

def g32p_supplierForest_node_064360 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_064360 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064360 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_136953 := by
  decide +kernel

theorem g32p_supplierForest_actual_064360 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064360) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064360
    g32p_supplierForest_actual_136953

def g32p_supplierForest_node_064379 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064379 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064379 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_140359 := by
  decide +kernel

theorem g32p_supplierForest_actual_064379 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064379) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_064379
    g32p_supplierForest_actual_140359

def g32p_supplierForest_node_064412 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064412 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064412 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_049849 := by
  decide +kernel

theorem g32p_supplierForest_actual_064412 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064412) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 0 g32p_supplierForest_edge_064412
    g32p_supplierForest_actual_049849

def g32p_supplierForest_node_064420 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064420 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064420 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130603 := by
  decide +kernel

theorem g32p_supplierForest_actual_064420 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064420) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 0 g32p_supplierForest_edge_064420
    g32p_supplierForest_actual_130603

def g32p_supplierForest_node_064426 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064426 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064426 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066444 := by
  decide +kernel

theorem g32p_supplierForest_actual_064426 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064426) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_064426
    g32p_supplierForest_actual_066444

def g32p_supplierForest_node_064465 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064465 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_006998 := by
  decide +kernel

theorem g32p_supplierForest_actual_064465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064465) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_064465
    g32p_supplierForest_actual_006998

def g32p_supplierForest_node_064486 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_064486 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064486 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131226 := by
  decide +kernel

theorem g32p_supplierForest_actual_064486 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064486) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 0 g32p_supplierForest_edge_064486
    g32p_supplierForest_actual_131226

def g32p_supplierForest_node_064526 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064526 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064526 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_130603 := by
  decide +kernel

theorem g32p_supplierForest_actual_064526 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064526) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 2 g32p_supplierForest_edge_064526
    g32p_supplierForest_actual_130603

def g32p_supplierForest_node_064531 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064531 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_052846 := by
  decide +kernel

theorem g32p_supplierForest_actual_064531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064531) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_064531
    g32p_supplierForest_actual_052846

def g32p_supplierForest_node_064546 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064546 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064546 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138383 := by
  decide +kernel

theorem g32p_supplierForest_actual_064546 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064546) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_064546
    g32p_supplierForest_actual_138383

def g32p_supplierForest_node_064592 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064592 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_005773 := by
  decide +kernel

theorem g32p_supplierForest_actual_064592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064592) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_064592
    g32p_supplierForest_actual_005773

def g32p_supplierForest_node_064606 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064606 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064606 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_048334 := by
  decide +kernel

theorem g32p_supplierForest_actual_064606 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064606) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_064606
    g32p_supplierForest_actual_048334

def g32p_supplierForest_node_064626 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064626 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064626 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051304 := by
  decide +kernel

theorem g32p_supplierForest_actual_064626 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064626) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 3 g32p_supplierForest_edge_064626
    g32p_supplierForest_actual_051304

def g32p_supplierForest_node_064639 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064639 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064639 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048772 := by
  decide +kernel

theorem g32p_supplierForest_actual_064639 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064639) ∧
        IsConj g (g32p_literalRepresentative 19) := by
  exact g32p_archive_step_lift _ _ 19 3 g32p_supplierForest_edge_064639
    g32p_supplierForest_actual_048772

def g32p_supplierForest_node_064645 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064645 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066132 := by
  decide +kernel

theorem g32p_supplierForest_actual_064645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064645) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_064645
    g32p_supplierForest_actual_066132

def g32p_supplierForest_node_064666 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064666 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_053002 := by
  decide +kernel

theorem g32p_supplierForest_actual_064666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064666) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_064666
    g32p_supplierForest_actual_053002

def g32p_supplierForest_node_064674 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064674 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064674 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_007943 := by
  decide +kernel

theorem g32p_supplierForest_actual_064674 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064674) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_064674
    g32p_supplierForest_actual_007943

def g32p_supplierForest_node_064718 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_064718 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064718 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051484 := by
  decide +kernel

theorem g32p_supplierForest_actual_064718 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064718) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_064718
    g32p_supplierForest_actual_051484

def g32p_supplierForest_node_064721 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064721 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064721 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_143896 := by
  decide +kernel

theorem g32p_supplierForest_actual_064721 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064721) ∧
        IsConj g (g32p_literalRepresentative 78) := by
  exact g32p_archive_step_lift _ _ 78 2 g32p_supplierForest_edge_064721
    g32p_supplierForest_actual_143896

def g32p_supplierForest_node_064732 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064732 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063368 := by
  decide +kernel

theorem g32p_supplierForest_actual_064732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064732) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_064732
    g32p_supplierForest_actual_063368

def g32p_supplierForest_node_064750 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064750 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064750 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065187 := by
  decide +kernel

theorem g32p_supplierForest_actual_064750 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064750) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_064750
    g32p_supplierForest_actual_065187

def g32p_supplierForest_node_064782 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064782 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064782 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008684 := by
  decide +kernel

theorem g32p_supplierForest_actual_064782 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064782) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_064782
    g32p_supplierForest_actual_008684

def g32p_supplierForest_node_064785 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064785 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131766 := by
  decide +kernel

theorem g32p_supplierForest_actual_064785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064785) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_064785
    g32p_supplierForest_actual_131766

def g32p_supplierForest_node_064832 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064832 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064832 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_054596 := by
  decide +kernel

theorem g32p_supplierForest_actual_064832 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064832) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_064832
    g32p_supplierForest_actual_054596

def g32p_supplierForest_node_064838 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064838 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064838 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067147 := by
  decide +kernel

theorem g32p_supplierForest_actual_064838 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064838) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_064838
    g32p_supplierForest_actual_067147

def g32p_supplierForest_node_064868 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064868 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064868 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064862 := by
  decide +kernel

theorem g32p_supplierForest_actual_064868 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064868) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_064868
    g32p_supplierForest_actual_064862

def g32p_supplierForest_node_064886 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064886 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064429 := by
  decide +kernel

theorem g32p_supplierForest_actual_064886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064886) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_064886
    g32p_supplierForest_actual_064429

def g32p_supplierForest_node_064907 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_064907 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064907 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_046597 := by
  decide +kernel

theorem g32p_supplierForest_actual_064907 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064907) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_064907
    g32p_supplierForest_actual_046597

def g32p_supplierForest_node_064977 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_064977 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064977 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_131931 := by
  decide +kernel

theorem g32p_supplierForest_actual_064977 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064977) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_064977
    g32p_supplierForest_actual_131931

def g32p_supplierForest_node_064990 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_064990 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064990 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062619 := by
  decide +kernel

theorem g32p_supplierForest_actual_064990 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064990) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_064990
    g32p_supplierForest_actual_062619

def g32p_supplierForest_node_065036 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_065036 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065036 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067454 := by
  decide +kernel

theorem g32p_supplierForest_actual_065036 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065036) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_065036
    g32p_supplierForest_actual_067454

def g32p_supplierForest_node_065129 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065129 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065129 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132078 := by
  decide +kernel

theorem g32p_supplierForest_actual_065129 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065129) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_065129
    g32p_supplierForest_actual_132078

def g32p_supplierForest_node_065190 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_065190 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065190 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_070150 := by
  decide +kernel

theorem g32p_supplierForest_actual_065190 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065190) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_065190
    g32p_supplierForest_actual_070150

def g32p_supplierForest_node_065202 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_065202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065202 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058418 := by
  decide +kernel

theorem g32p_supplierForest_actual_065202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065202) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_065202
    g32p_supplierForest_actual_058418

def g32p_supplierForest_node_065213 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065213 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065213 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009199 := by
  decide +kernel

theorem g32p_supplierForest_actual_065213 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065213) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 2 g32p_supplierForest_edge_065213
    g32p_supplierForest_actual_009199

def g32p_supplierForest_node_065315 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_065315 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065315 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062289 := by
  decide +kernel

theorem g32p_supplierForest_actual_065315 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065315) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_065315
    g32p_supplierForest_actual_062289

def g32p_supplierForest_node_065357 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065357 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065357 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_066431 := by
  decide +kernel

theorem g32p_supplierForest_actual_065357 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065357) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065357
    g32p_supplierForest_actual_066431

def g32p_supplierForest_node_065361 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065361 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064637 := by
  decide +kernel

theorem g32p_supplierForest_actual_065361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065361) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_065361
    g32p_supplierForest_actual_064637

def g32p_supplierForest_node_065402 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065402 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065402 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062183 := by
  decide +kernel

theorem g32p_supplierForest_actual_065402 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065402) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_065402
    g32p_supplierForest_actual_062183

def g32p_supplierForest_node_065412 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065412 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065412 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068403 := by
  decide +kernel

theorem g32p_supplierForest_actual_065412 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065412) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_065412
    g32p_supplierForest_actual_068403

def g32p_supplierForest_node_065413 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065413 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065413 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068404 := by
  decide +kernel

theorem g32p_supplierForest_actual_065413 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065413) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 1 g32p_supplierForest_edge_065413
    g32p_supplierForest_actual_068404

def g32p_supplierForest_node_065419 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065419 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132318 := by
  decide +kernel

theorem g32p_supplierForest_actual_065419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065419) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_065419
    g32p_supplierForest_actual_132318

def g32p_supplierForest_node_065421 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065421 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058638 := by
  decide +kernel

theorem g32p_supplierForest_actual_065421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065421) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 0 g32p_supplierForest_edge_065421
    g32p_supplierForest_actual_058638

def g32p_supplierForest_node_065430 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065430 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065430 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068383 := by
  decide +kernel

theorem g32p_supplierForest_actual_065430 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065430) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 1 g32p_supplierForest_edge_065430
    g32p_supplierForest_actual_068383

def g32p_supplierForest_node_065440 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065440 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_067565 := by
  decide +kernel

theorem g32p_supplierForest_actual_065440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065440) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_065440
    g32p_supplierForest_actual_067565

def g32p_supplierForest_node_065473 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065473 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065473 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068514 := by
  decide +kernel

theorem g32p_supplierForest_actual_065473 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065473) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_065473
    g32p_supplierForest_actual_068514

def g32p_supplierForest_node_065478 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065478 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065478 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067701 := by
  decide +kernel

theorem g32p_supplierForest_actual_065478 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065478) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065478
    g32p_supplierForest_actual_067701

def g32p_supplierForest_node_065494 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065494 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065494 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051068 := by
  decide +kernel

theorem g32p_supplierForest_actual_065494 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065494) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_065494
    g32p_supplierForest_actual_051068

def g32p_supplierForest_node_065500 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_065500 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065500 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063162 := by
  decide +kernel

theorem g32p_supplierForest_actual_065500 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065500) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_065500
    g32p_supplierForest_actual_063162

def g32p_supplierForest_node_065506 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065506 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065506 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056876 := by
  decide +kernel

theorem g32p_supplierForest_actual_065506 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065506) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_065506
    g32p_supplierForest_actual_056876

def g32p_supplierForest_node_065520 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_065520 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065520 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068611 := by
  decide +kernel

theorem g32p_supplierForest_actual_065520 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065520) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_065520
    g32p_supplierForest_actual_068611

def g32p_supplierForest_node_065534 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065534 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065534 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_011016 := by
  decide +kernel

theorem g32p_supplierForest_actual_065534 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065534) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 1 g32p_supplierForest_edge_065534
    g32p_supplierForest_actual_011016

def g32p_supplierForest_node_065568 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065568 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065568 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_050997 := by
  decide +kernel

theorem g32p_supplierForest_actual_065568 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065568) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_065568
    g32p_supplierForest_actual_050997

def g32p_supplierForest_node_065569 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065569 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132447 := by
  decide +kernel

theorem g32p_supplierForest_actual_065569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065569) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_065569
    g32p_supplierForest_actual_132447

def g32p_supplierForest_node_065580 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065580 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065580 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063260 := by
  decide +kernel

theorem g32p_supplierForest_actual_065580 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065580) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065580
    g32p_supplierForest_actual_063260

def g32p_supplierForest_node_065587 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065587 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065587 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132462 := by
  decide +kernel

theorem g32p_supplierForest_actual_065587 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065587) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_065587
    g32p_supplierForest_actual_132462

def g32p_supplierForest_node_065610 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065610 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065610 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_047102 := by
  decide +kernel

theorem g32p_supplierForest_actual_065610 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065610) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_065610
    g32p_supplierForest_actual_047102

def g32p_supplierForest_node_065633 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065633 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065633 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_141856 := by
  decide +kernel

theorem g32p_supplierForest_actual_065633 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065633) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_065633
    g32p_supplierForest_actual_141856

def g32p_supplierForest_node_065636 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065636 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065636 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068807 := by
  decide +kernel

theorem g32p_supplierForest_actual_065636 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065636) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_065636
    g32p_supplierForest_actual_068807

def g32p_supplierForest_node_065664 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065664 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062690 := by
  decide +kernel

theorem g32p_supplierForest_actual_065664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065664) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_065664
    g32p_supplierForest_actual_062690

def g32p_supplierForest_node_065668 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065668 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065668 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_064883 := by
  decide +kernel

theorem g32p_supplierForest_actual_065668 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065668) ∧
        IsConj g (g32p_literalRepresentative 23) := by
  exact g32p_archive_step_lift _ _ 23 0 g32p_supplierForest_edge_065668
    g32p_supplierForest_actual_064883

def g32p_supplierForest_node_065689 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065689 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065689 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010824 := by
  decide +kernel

theorem g32p_supplierForest_actual_065689 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065689) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_065689
    g32p_supplierForest_actual_010824

def g32p_supplierForest_node_065696 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065696 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065696 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067701 := by
  decide +kernel

theorem g32p_supplierForest_actual_065696 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065696) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065696
    g32p_supplierForest_actual_067701

def g32p_supplierForest_node_065709 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065709 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065709 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063306 := by
  decide +kernel

theorem g32p_supplierForest_actual_065709 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065709) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_065709
    g32p_supplierForest_actual_063306

def g32p_supplierForest_node_065716 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065716 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059922 := by
  decide +kernel

theorem g32p_supplierForest_actual_065716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065716) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_065716
    g32p_supplierForest_actual_059922

def g32p_supplierForest_node_065719 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065719 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065719 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132561 := by
  decide +kernel

theorem g32p_supplierForest_actual_065719 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065719) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_065719
    g32p_supplierForest_actual_132561

def g32p_supplierForest_node_065731 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065731 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065731 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_139658 := by
  decide +kernel

theorem g32p_supplierForest_actual_065731 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065731) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 3 g32p_supplierForest_edge_065731
    g32p_supplierForest_actual_139658

def g32p_supplierForest_node_065749 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065749 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065749 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_052017 := by
  decide +kernel

theorem g32p_supplierForest_actual_065749 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065749) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_065749
    g32p_supplierForest_actual_052017

def g32p_supplierForest_node_065773 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065773 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069044 := by
  decide +kernel

theorem g32p_supplierForest_actual_065773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065773) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_065773
    g32p_supplierForest_actual_069044

def g32p_supplierForest_node_065798 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩]]

theorem g32p_supplierForest_edge_065798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065798 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128310 := by
  decide +kernel

theorem g32p_supplierForest_actual_065798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065798) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_065798
    g32p_supplierForest_actual_128310

def g32p_supplierForest_node_065807 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065807 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060725 := by
  decide +kernel

theorem g32p_supplierForest_actual_065807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065807) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_065807
    g32p_supplierForest_actual_060725

def g32p_supplierForest_node_065818 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065818 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_060412 := by
  decide +kernel

theorem g32p_supplierForest_actual_065818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065818) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_065818
    g32p_supplierForest_actual_060412

def g32p_supplierForest_node_065866 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065866 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065866 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059950 := by
  decide +kernel

theorem g32p_supplierForest_actual_065866 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065866) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 1 g32p_supplierForest_edge_065866
    g32p_supplierForest_actual_059950

def g32p_supplierForest_node_065877 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065877 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132709 := by
  decide +kernel

theorem g32p_supplierForest_actual_065877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065877) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 0 g32p_supplierForest_edge_065877
    g32p_supplierForest_actual_132709

def g32p_supplierForest_node_065888 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_065888 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065888 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063919 := by
  decide +kernel

theorem g32p_supplierForest_actual_065888 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065888) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_065888
    g32p_supplierForest_actual_063919

def g32p_supplierForest_node_065925 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065925 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065925 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_143034 := by
  decide +kernel

theorem g32p_supplierForest_actual_065925 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065925) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_065925
    g32p_supplierForest_actual_143034

def g32p_supplierForest_node_065933 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_065933 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065933 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069364 := by
  decide +kernel

theorem g32p_supplierForest_actual_065933 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065933) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_065933
    g32p_supplierForest_actual_069364

def g32p_supplierForest_node_065935 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065935 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065935 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070199 := by
  decide +kernel

theorem g32p_supplierForest_actual_065935 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065935) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_065935
    g32p_supplierForest_actual_070199

def g32p_supplierForest_node_065942 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065942 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065942 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071172 := by
  decide +kernel

theorem g32p_supplierForest_actual_065942 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065942) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_065942
    g32p_supplierForest_actual_071172

def g32p_supplierForest_node_066003 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066003 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066003 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070338 := by
  decide +kernel

theorem g32p_supplierForest_actual_066003 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066003) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_066003
    g32p_supplierForest_actual_070338

def g32p_supplierForest_node_066034 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066034 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066034 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012184 := by
  decide +kernel

theorem g32p_supplierForest_actual_066034 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066034) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_066034
    g32p_supplierForest_actual_012184

def g32p_supplierForest_node_066035 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066035 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_143850 := by
  decide +kernel

theorem g32p_supplierForest_actual_066035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066035) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_066035
    g32p_supplierForest_actual_143850

def g32p_supplierForest_node_066091 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066091 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066091 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132877 := by
  decide +kernel

theorem g32p_supplierForest_actual_066091 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066091) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_066091
    g32p_supplierForest_actual_132877

def g32p_supplierForest_node_066107 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066107 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066107 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_009837 := by
  decide +kernel

theorem g32p_supplierForest_actual_066107 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066107) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_066107
    g32p_supplierForest_actual_009837

def g32p_supplierForest_node_066114 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066114 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066114 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_045155 := by
  decide +kernel

theorem g32p_supplierForest_actual_066114 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066114) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_066114
    g32p_supplierForest_actual_045155

def g32p_supplierForest_node_066147 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066147 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066147 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069688 := by
  decide +kernel

theorem g32p_supplierForest_actual_066147 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066147) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_066147
    g32p_supplierForest_actual_069688

def g32p_supplierForest_node_066159 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066159 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_012253 := by
  decide +kernel

theorem g32p_supplierForest_actual_066159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066159) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_066159
    g32p_supplierForest_actual_012253

def g32p_supplierForest_node_066175 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066175 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010300 := by
  decide +kernel

theorem g32p_supplierForest_actual_066175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066175) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_066175
    g32p_supplierForest_actual_010300

def g32p_supplierForest_node_066202 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066202 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066202 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071309 := by
  decide +kernel

theorem g32p_supplierForest_actual_066202 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066202) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_066202
    g32p_supplierForest_actual_071309

def g32p_supplierForest_node_066241 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066241 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066241 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049375 := by
  decide +kernel

theorem g32p_supplierForest_actual_066241 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066241) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 3 g32p_supplierForest_edge_066241
    g32p_supplierForest_actual_049375

def g32p_supplierForest_node_066246 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066246 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_061830 := by
  decide +kernel

theorem g32p_supplierForest_actual_066246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066246) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_066246
    g32p_supplierForest_actual_061830

def g32p_supplierForest_node_066247 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066247 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066247 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_009939 := by
  decide +kernel

theorem g32p_supplierForest_actual_066247 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066247) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066247
    g32p_supplierForest_actual_009939

def g32p_supplierForest_node_066317 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066317 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066317 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133074 := by
  decide +kernel

theorem g32p_supplierForest_actual_066317 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066317) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_066317
    g32p_supplierForest_actual_133074

def g32p_supplierForest_node_066322 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066322 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066322 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059922 := by
  decide +kernel

theorem g32p_supplierForest_actual_066322 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066322) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_066322
    g32p_supplierForest_actual_059922

def g32p_supplierForest_node_066330 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066330 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066330 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058959 := by
  decide +kernel

theorem g32p_supplierForest_actual_066330 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066330) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_066330
    g32p_supplierForest_actual_058959

def g32p_supplierForest_node_066371 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066371 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133108 := by
  decide +kernel

theorem g32p_supplierForest_actual_066371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066371) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_066371
    g32p_supplierForest_actual_133108

def g32p_supplierForest_node_066414 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066414 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066414 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059089 := by
  decide +kernel

theorem g32p_supplierForest_actual_066414 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066414) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_066414
    g32p_supplierForest_actual_059089

def g32p_supplierForest_node_066453 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066453 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066453 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067040 := by
  decide +kernel

theorem g32p_supplierForest_actual_066453 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066453) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_066453
    g32p_supplierForest_actual_067040

def g32p_supplierForest_node_066469 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066469 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066469 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_046449 := by
  decide +kernel

theorem g32p_supplierForest_actual_066469 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066469) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_066469
    g32p_supplierForest_actual_046449

def g32p_supplierForest_node_066545 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066545 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066545 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_054367 := by
  decide +kernel

theorem g32p_supplierForest_actual_066545 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066545) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 0 g32p_supplierForest_edge_066545
    g32p_supplierForest_actual_054367

def g32p_supplierForest_node_066569 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066569 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133271 := by
  decide +kernel

theorem g32p_supplierForest_actual_066569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066569) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_066569
    g32p_supplierForest_actual_133271

def g32p_supplierForest_node_066570 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066570 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066570 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065062 := by
  decide +kernel

theorem g32p_supplierForest_actual_066570 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066570) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_066570
    g32p_supplierForest_actual_065062

def g32p_supplierForest_node_066572 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066572 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066572 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061723 := by
  decide +kernel

theorem g32p_supplierForest_actual_066572 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066572) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_066572
    g32p_supplierForest_actual_061723

def g32p_supplierForest_node_066573 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066573 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066573 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070134 := by
  decide +kernel

theorem g32p_supplierForest_actual_066573 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066573) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_066573
    g32p_supplierForest_actual_070134

def g32p_supplierForest_node_066587 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066587 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066587 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_065449 := by
  decide +kernel

theorem g32p_supplierForest_actual_066587 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066587) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_066587
    g32p_supplierForest_actual_065449

def g32p_supplierForest_node_066592 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066592 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070404 := by
  decide +kernel

theorem g32p_supplierForest_actual_066592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066592) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_066592
    g32p_supplierForest_actual_070404

def g32p_supplierForest_node_066609 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066609 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066609 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070428 := by
  decide +kernel

theorem g32p_supplierForest_actual_066609 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066609) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_066609
    g32p_supplierForest_actual_070428

def g32p_supplierForest_node_066612 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066612 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066612 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070430 := by
  decide +kernel

theorem g32p_supplierForest_actual_066612 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066612) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_066612
    g32p_supplierForest_actual_070430

def g32p_supplierForest_node_066637 : HurwitzPrymRex_Mat :=
  ![![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066637 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045639 := by
  decide +kernel

theorem g32p_supplierForest_actual_066637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066637) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 3 g32p_supplierForest_edge_066637
    g32p_supplierForest_actual_045639

def g32p_supplierForest_node_066738 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_066738 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066738 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_068553 := by
  decide +kernel

theorem g32p_supplierForest_actual_066738 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066738) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_066738
    g32p_supplierForest_actual_068553

def g32p_supplierForest_node_066742 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066742 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_053701 := by
  decide +kernel

theorem g32p_supplierForest_actual_066742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066742) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_066742
    g32p_supplierForest_actual_053701

def g32p_supplierForest_node_066754 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066754 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068403 := by
  decide +kernel

theorem g32p_supplierForest_actual_066754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066754) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_066754
    g32p_supplierForest_actual_068403

def g32p_supplierForest_node_066756 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, -1⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066756 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066756 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071398 := by
  decide +kernel

theorem g32p_supplierForest_actual_066756 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066756) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_066756
    g32p_supplierForest_actual_071398

def g32p_supplierForest_node_066808 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066808 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066808 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066829 := by
  decide +kernel

theorem g32p_supplierForest_actual_066808 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066808) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_066808
    g32p_supplierForest_actual_066829

def g32p_supplierForest_node_066824 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_066824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066824 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051905 := by
  decide +kernel

theorem g32p_supplierForest_actual_066824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066824) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_066824
    g32p_supplierForest_actual_051905

def g32p_supplierForest_node_066836 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨2, 1⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066836 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066836 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070763 := by
  decide +kernel

theorem g32p_supplierForest_actual_066836 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066836) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_066836
    g32p_supplierForest_actual_070763

def g32p_supplierForest_node_066886 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066886 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066886 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134447 := by
  decide +kernel

theorem g32p_supplierForest_actual_066886 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066886) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_066886
    g32p_supplierForest_actual_134447

def g32p_supplierForest_node_066894 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066894 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066894 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_008862 := by
  decide +kernel

theorem g32p_supplierForest_actual_066894 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066894) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_066894
    g32p_supplierForest_actual_008862

def g32p_supplierForest_node_066910 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_066910 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066910 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_070909 := by
  decide +kernel

theorem g32p_supplierForest_actual_066910 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066910) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_066910
    g32p_supplierForest_actual_070909

def g32p_supplierForest_node_066913 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066913 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066913 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_135253 := by
  decide +kernel

theorem g32p_supplierForest_actual_066913 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066913) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_066913
    g32p_supplierForest_actual_135253

def g32p_supplierForest_node_066927 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066927 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_058638 := by
  decide +kernel

theorem g32p_supplierForest_actual_066927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066927) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_066927
    g32p_supplierForest_actual_058638

def g32p_supplierForest_node_066978 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066978 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_062011 := by
  decide +kernel

theorem g32p_supplierForest_actual_066978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066978) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 3 g32p_supplierForest_edge_066978
    g32p_supplierForest_actual_062011

def g32p_supplierForest_node_066989 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_066989 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066989 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_058050 := by
  decide +kernel

theorem g32p_supplierForest_actual_066989 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066989) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_066989
    g32p_supplierForest_actual_058050

def g32p_supplierForest_node_066993 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_066993 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066993 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045786 := by
  decide +kernel

theorem g32p_supplierForest_actual_066993 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066993) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_066993
    g32p_supplierForest_actual_045786

def g32p_supplierForest_node_067033 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067033 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067033 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069939 := by
  decide +kernel

theorem g32p_supplierForest_actual_067033 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067033) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_067033
    g32p_supplierForest_actual_069939

def g32p_supplierForest_node_067057 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067057 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067057 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056755 := by
  decide +kernel

theorem g32p_supplierForest_actual_067057 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067057) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_067057
    g32p_supplierForest_actual_056755

def g32p_supplierForest_node_067059 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067059 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_065062 := by
  decide +kernel

theorem g32p_supplierForest_actual_067059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067059) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_067059
    g32p_supplierForest_actual_065062

def g32p_supplierForest_node_067096 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067096 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067096 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_050200 := by
  decide +kernel

theorem g32p_supplierForest_actual_067096 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067096) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_067096
    g32p_supplierForest_actual_050200

def g32p_supplierForest_node_067134 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067134 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067134 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133798 := by
  decide +kernel

theorem g32p_supplierForest_actual_067134 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067134) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_067134
    g32p_supplierForest_actual_133798

def g32p_supplierForest_node_067185 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-2, 0⟩, ⟨-1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067185 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067185 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010062 := by
  decide +kernel

theorem g32p_supplierForest_actual_067185 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067185) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067185
    g32p_supplierForest_actual_010062

def g32p_supplierForest_node_067198 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067198 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067198 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_010068 := by
  decide +kernel

theorem g32p_supplierForest_actual_067198 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067198) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_067198
    g32p_supplierForest_actual_010068

def g32p_supplierForest_node_067226 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067226 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067226 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_055214 := by
  decide +kernel

theorem g32p_supplierForest_actual_067226 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067226) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067226
    g32p_supplierForest_actual_055214

def g32p_supplierForest_node_067227 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨2, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_067227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067227 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_055047 := by
  decide +kernel

theorem g32p_supplierForest_actual_067227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067227) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 3 g32p_supplierForest_edge_067227
    g32p_supplierForest_actual_055047

def g32p_supplierForest_node_067244 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067244 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067244 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_141118 := by
  decide +kernel

theorem g32p_supplierForest_actual_067244 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067244) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_067244
    g32p_supplierForest_actual_141118

def g32p_supplierForest_node_067272 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067272 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067272 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067061 := by
  decide +kernel

theorem g32p_supplierForest_actual_067272 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067272) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_067272
    g32p_supplierForest_actual_067061

def g32p_supplierForest_node_067284 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067284 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_066619 := by
  decide +kernel

theorem g32p_supplierForest_actual_067284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067284) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067284
    g32p_supplierForest_actual_066619

def g32p_supplierForest_node_067316 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067316 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067316 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050728 := by
  decide +kernel

theorem g32p_supplierForest_actual_067316 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067316) ∧
        IsConj g (g32p_literalRepresentative 24) := by
  exact g32p_archive_step_lift _ _ 24 1 g32p_supplierForest_edge_067316
    g32p_supplierForest_actual_050728

def g32p_supplierForest_node_067385 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067385 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067385 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_071623 := by
  decide +kernel

theorem g32p_supplierForest_actual_067385 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067385) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 1 g32p_supplierForest_edge_067385
    g32p_supplierForest_actual_071623

def g32p_supplierForest_node_067396 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067396 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067396 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047696 := by
  decide +kernel

theorem g32p_supplierForest_actual_067396 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067396) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_067396
    g32p_supplierForest_actual_047696

def g32p_supplierForest_node_067416 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067416 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067416 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_048039 := by
  decide +kernel

theorem g32p_supplierForest_actual_067416 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067416) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067416
    g32p_supplierForest_actual_048039

def g32p_supplierForest_node_067419 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067419 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067419 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067031 := by
  decide +kernel

theorem g32p_supplierForest_actual_067419 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067419) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_067419
    g32p_supplierForest_actual_067031

def g32p_supplierForest_node_067480 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067480 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067480 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_053043 := by
  decide +kernel

theorem g32p_supplierForest_actual_067480 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067480) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_067480
    g32p_supplierForest_actual_053043

def g32p_supplierForest_node_067483 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067483 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_054367 := by
  decide +kernel

theorem g32p_supplierForest_actual_067483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067483) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_067483
    g32p_supplierForest_actual_054367

def g32p_supplierForest_node_067514 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067514 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067514 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_047495 := by
  decide +kernel

theorem g32p_supplierForest_actual_067514 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067514) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_067514
    g32p_supplierForest_actual_047495

def g32p_supplierForest_node_067535 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_067535 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067535 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_044571 := by
  decide +kernel

theorem g32p_supplierForest_actual_067535 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067535) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_067535
    g32p_supplierForest_actual_044571

def g32p_supplierForest_node_067562 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_067562 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067562 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_067565 := by
  decide +kernel

theorem g32p_supplierForest_actual_067562 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067562) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 3 g32p_supplierForest_edge_067562
    g32p_supplierForest_actual_067565

def g32p_supplierForest_node_067585 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_067585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067585 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_008776 := by
  decide +kernel

theorem g32p_supplierForest_actual_067585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067585) ∧
        IsConj g (g32p_literalRepresentative 18) := by
  exact g32p_archive_step_lift _ _ 18 2 g32p_supplierForest_edge_067585
    g32p_supplierForest_actual_008776

def g32p_supplierForest_node_067605 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067605 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067605 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059649 := by
  decide +kernel

theorem g32p_supplierForest_actual_067605 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067605) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_067605
    g32p_supplierForest_actual_059649

def g32p_supplierForest_node_067608 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067608 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067608 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134206 := by
  decide +kernel

theorem g32p_supplierForest_actual_067608 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067608) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_067608
    g32p_supplierForest_actual_134206

def g32p_supplierForest_node_067620 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067620 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067620 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061527 := by
  decide +kernel

theorem g32p_supplierForest_actual_067620 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067620) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_067620
    g32p_supplierForest_actual_061527

def g32p_supplierForest_node_067621 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067621 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134216 := by
  decide +kernel

theorem g32p_supplierForest_actual_067621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067621) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_067621
    g32p_supplierForest_actual_134216

def g32p_supplierForest_node_067681 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_067681 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067681 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058741 := by
  decide +kernel

theorem g32p_supplierForest_actual_067681 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067681) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_067681
    g32p_supplierForest_actual_058741

def g32p_supplierForest_node_067685 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067685 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067685 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_131140 := by
  decide +kernel

theorem g32p_supplierForest_actual_067685 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067685) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_067685
    g32p_supplierForest_actual_131140

def g32p_supplierForest_node_067690 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067690 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067690 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_052997 := by
  decide +kernel

theorem g32p_supplierForest_actual_067690 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067690) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_067690
    g32p_supplierForest_actual_052997

def g32p_supplierForest_node_067697 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067697 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067697 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062619 := by
  decide +kernel

theorem g32p_supplierForest_actual_067697 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067697) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_067697
    g32p_supplierForest_actual_062619

def g32p_supplierForest_node_067708 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067708 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067708 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_046177 := by
  decide +kernel

theorem g32p_supplierForest_actual_067708 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067708) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_067708
    g32p_supplierForest_actual_046177

def g32p_supplierForest_node_067746 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_067746 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067746 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060174 := by
  decide +kernel

theorem g32p_supplierForest_actual_067746 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067746) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 2 g32p_supplierForest_edge_067746
    g32p_supplierForest_actual_060174

def g32p_supplierForest_node_067806 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_067806 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067806 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070056 := by
  decide +kernel

theorem g32p_supplierForest_actual_067806 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067806) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_067806
    g32p_supplierForest_actual_070056

def g32p_supplierForest_node_067845 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067845 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067845 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_065314 := by
  decide +kernel

theorem g32p_supplierForest_actual_067845 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067845) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067845
    g32p_supplierForest_actual_065314

def g32p_supplierForest_node_067847 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067847 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067847 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070780 := by
  decide +kernel

theorem g32p_supplierForest_actual_067847 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067847) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 0 g32p_supplierForest_edge_067847
    g32p_supplierForest_actual_070780

def g32p_supplierForest_node_067849 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067849 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067849 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_139272 := by
  decide +kernel

theorem g32p_supplierForest_actual_067849 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067849) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 1 g32p_supplierForest_edge_067849
    g32p_supplierForest_actual_139272

def g32p_supplierForest_node_067852 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067852 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067852 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059319 := by
  decide +kernel

theorem g32p_supplierForest_actual_067852 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067852) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067852
    g32p_supplierForest_actual_059319

def g32p_supplierForest_node_067854 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_067854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067854 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_067772 := by
  decide +kernel

theorem g32p_supplierForest_actual_067854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067854) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 1 g32p_supplierForest_edge_067854
    g32p_supplierForest_actual_067772

def g32p_supplierForest_node_067914 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067914 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067914 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063349 := by
  decide +kernel

theorem g32p_supplierForest_actual_067914 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067914) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_067914
    g32p_supplierForest_actual_063349

def g32p_supplierForest_node_067915 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067915 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067915 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_069094 := by
  decide +kernel

theorem g32p_supplierForest_actual_067915 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067915) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_067915
    g32p_supplierForest_actual_069094

def g32p_supplierForest_node_067927 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067927 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067927 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_134240 := by
  decide +kernel

theorem g32p_supplierForest_actual_067927 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067927) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_067927
    g32p_supplierForest_actual_134240

def g32p_supplierForest_node_067953 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, -1⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067953 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067953 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061404 := by
  decide +kernel

theorem g32p_supplierForest_actual_067953 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067953) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_067953
    g32p_supplierForest_actual_061404

def g32p_supplierForest_node_067961 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067961 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067961 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_063882 := by
  decide +kernel

theorem g32p_supplierForest_actual_067961 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067961) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_067961
    g32p_supplierForest_actual_063882

def g32p_supplierForest_node_067966 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067966 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067966 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_132309 := by
  decide +kernel

theorem g32p_supplierForest_actual_067966 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067966) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_067966
    g32p_supplierForest_actual_132309

def g32p_supplierForest_node_067972 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_067972 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067972 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063578 := by
  decide +kernel

theorem g32p_supplierForest_actual_067972 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067972) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_067972
    g32p_supplierForest_actual_063578

def g32p_supplierForest_node_067987 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067987 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067987 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134488 := by
  decide +kernel

theorem g32p_supplierForest_actual_067987 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067987) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 0 g32p_supplierForest_edge_067987
    g32p_supplierForest_actual_134488

def g32p_supplierForest_node_068042 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068042 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068042 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130215 := by
  decide +kernel

theorem g32p_supplierForest_actual_068042 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068042) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_068042
    g32p_supplierForest_actual_130215

def g32p_supplierForest_node_068059 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068059 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_069461 := by
  decide +kernel

theorem g32p_supplierForest_actual_068059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068059) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 1 g32p_supplierForest_edge_068059
    g32p_supplierForest_actual_069461

def g32p_supplierForest_node_068119 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068119 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_045705 := by
  decide +kernel

theorem g32p_supplierForest_actual_068119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068119) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068119
    g32p_supplierForest_actual_045705

def g32p_supplierForest_node_068156 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-2, 0⟩, ⟨-2, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068156 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068156 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064517 := by
  decide +kernel

theorem g32p_supplierForest_actual_068156 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068156) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_068156
    g32p_supplierForest_actual_064517

def g32p_supplierForest_node_068197 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068197 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068197 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009706 := by
  decide +kernel

theorem g32p_supplierForest_actual_068197 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068197) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_068197
    g32p_supplierForest_actual_009706

def g32p_supplierForest_node_068209 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068209 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068209 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_056713 := by
  decide +kernel

theorem g32p_supplierForest_actual_068209 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068209) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068209
    g32p_supplierForest_actual_056713

def g32p_supplierForest_node_068231 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068231 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_064015 := by
  decide +kernel

theorem g32p_supplierForest_actual_068231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068231) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_068231
    g32p_supplierForest_actual_064015

def g32p_supplierForest_node_068246 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068246 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068246 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_137242 := by
  decide +kernel

theorem g32p_supplierForest_actual_068246 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068246) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 3 g32p_supplierForest_edge_068246
    g32p_supplierForest_actual_137242

def g32p_supplierForest_node_068263 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068263 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_009733 := by
  decide +kernel

theorem g32p_supplierForest_actual_068263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068263) ∧
        IsConj g (g32p_literalRepresentative 6) := by
  exact g32p_archive_step_lift _ _ 6 2 g32p_supplierForest_edge_068263
    g32p_supplierForest_actual_009733

def g32p_supplierForest_node_068267 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-2, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068267 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068267 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048529 := by
  decide +kernel

theorem g32p_supplierForest_actual_068267 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068267) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_068267
    g32p_supplierForest_actual_048529

def g32p_supplierForest_node_068270 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068270 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_136825 := by
  decide +kernel

theorem g32p_supplierForest_actual_068270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068270) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 1 g32p_supplierForest_edge_068270
    g32p_supplierForest_actual_136825

def g32p_supplierForest_node_068273 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068273 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068273 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_053905 := by
  decide +kernel

theorem g32p_supplierForest_actual_068273 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068273) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_068273
    g32p_supplierForest_actual_053905

def g32p_supplierForest_node_068288 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068288 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068288 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_048056 := by
  decide +kernel

theorem g32p_supplierForest_actual_068288 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068288) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 2 g32p_supplierForest_edge_068288
    g32p_supplierForest_actual_048056

def g32p_supplierForest_node_068290 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068290 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068290 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011224 := by
  decide +kernel

theorem g32p_supplierForest_actual_068290 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068290) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_068290
    g32p_supplierForest_actual_011224

def g32p_supplierForest_node_068297 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068297 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068297 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_053213 := by
  decide +kernel

theorem g32p_supplierForest_actual_068297 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068297) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_068297
    g32p_supplierForest_actual_053213

def g32p_supplierForest_node_068306 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068306 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068306 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134742 := by
  decide +kernel

theorem g32p_supplierForest_actual_068306 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068306) ∧
        IsConj g (g32p_literalRepresentative 71) := by
  exact g32p_archive_step_lift _ _ 71 0 g32p_supplierForest_edge_068306
    g32p_supplierForest_actual_134742

def g32p_supplierForest_node_068338 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068338 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068338 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_132953 := by
  decide +kernel

theorem g32p_supplierForest_actual_068338 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068338) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_068338
    g32p_supplierForest_actual_132953

def g32p_supplierForest_node_068378 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068378 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068378 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071306 := by
  decide +kernel

theorem g32p_supplierForest_actual_068378 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068378) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_068378
    g32p_supplierForest_actual_071306

def g32p_supplierForest_node_068380 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068380 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066431 := by
  decide +kernel

theorem g32p_supplierForest_actual_068380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068380) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_068380
    g32p_supplierForest_actual_066431

def g32p_supplierForest_node_068396 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068396 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068396 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_060895 := by
  decide +kernel

theorem g32p_supplierForest_actual_068396 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068396) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_068396
    g32p_supplierForest_actual_060895

def g32p_supplierForest_node_068427 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068427 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068427 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062462 := by
  decide +kernel

theorem g32p_supplierForest_actual_068427 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068427) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_068427
    g32p_supplierForest_actual_062462

def g32p_supplierForest_node_068429 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨1, 2⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068429 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068429 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062916 := by
  decide +kernel

theorem g32p_supplierForest_actual_068429 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068429) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 2 g32p_supplierForest_edge_068429
    g32p_supplierForest_actual_062916

def g32p_supplierForest_node_068450 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068450 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068450 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_131064 := by
  decide +kernel

theorem g32p_supplierForest_actual_068450 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068450) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_068450
    g32p_supplierForest_actual_131064

def g32p_supplierForest_node_068464 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068464 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068464 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066634 := by
  decide +kernel

theorem g32p_supplierForest_actual_068464 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068464) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_068464
    g32p_supplierForest_actual_066634

def g32p_supplierForest_node_068515 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068515 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068515 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066847 := by
  decide +kernel

theorem g32p_supplierForest_actual_068515 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068515) ∧
        IsConj g (g32p_literalRepresentative 74) := by
  exact g32p_archive_step_lift _ _ 74 2 g32p_supplierForest_edge_068515
    g32p_supplierForest_actual_066847

def g32p_supplierForest_node_068519 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068519 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068519 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_129868 := by
  decide +kernel

theorem g32p_supplierForest_actual_068519 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068519) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 1 g32p_supplierForest_edge_068519
    g32p_supplierForest_actual_129868

def g32p_supplierForest_node_068523 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068523 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068523 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_136552 := by
  decide +kernel

theorem g32p_supplierForest_actual_068523 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068523) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 1 g32p_supplierForest_edge_068523
    g32p_supplierForest_actual_136552

def g32p_supplierForest_node_068529 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068529 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068529 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069744 := by
  decide +kernel

theorem g32p_supplierForest_actual_068529 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068529) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_068529
    g32p_supplierForest_actual_069744

def g32p_supplierForest_node_068552 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -2⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068552 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068552 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061279 := by
  decide +kernel

theorem g32p_supplierForest_actual_068552 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068552) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_068552
    g32p_supplierForest_actual_061279

def g32p_supplierForest_node_068558 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068558 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068558 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_129691 := by
  decide +kernel

theorem g32p_supplierForest_actual_068558 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068558) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 1 g32p_supplierForest_edge_068558
    g32p_supplierForest_actual_129691

def g32p_supplierForest_node_068563 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068563 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_066803 := by
  decide +kernel

theorem g32p_supplierForest_actual_068563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068563) ∧
        IsConj g (g32p_literalRepresentative 40) := by
  exact g32p_archive_step_lift _ _ 40 2 g32p_supplierForest_edge_068563
    g32p_supplierForest_actual_066803

def g32p_supplierForest_node_068568 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 2⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068568 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068568 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064484 := by
  decide +kernel

theorem g32p_supplierForest_actual_068568 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068568) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_068568
    g32p_supplierForest_actual_064484

def g32p_supplierForest_node_068569 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068569 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068569 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067127 := by
  decide +kernel

theorem g32p_supplierForest_actual_068569 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068569) ∧
        IsConj g (g32p_literalRepresentative 75) := by
  exact g32p_archive_step_lift _ _ 75 2 g32p_supplierForest_edge_068569
    g32p_supplierForest_actual_067127

def g32p_supplierForest_node_068586 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068586 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068586 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_051071 := by
  decide +kernel

theorem g32p_supplierForest_actual_068586 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068586) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_068586
    g32p_supplierForest_actual_051071

def g32p_supplierForest_node_068590 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068590 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068590 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_064506 := by
  decide +kernel

theorem g32p_supplierForest_actual_068590 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068590) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_068590
    g32p_supplierForest_actual_064506

def g32p_supplierForest_node_068633 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068633 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068633 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070430 := by
  decide +kernel

theorem g32p_supplierForest_actual_068633 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068633) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_068633
    g32p_supplierForest_actual_070430

def g32p_supplierForest_node_068635 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068635 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068635 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_065079 := by
  decide +kernel

theorem g32p_supplierForest_actual_068635 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068635) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 3 g32p_supplierForest_edge_068635
    g32p_supplierForest_actual_065079

def g32p_supplierForest_node_068636 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_068636 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068636 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_010542 := by
  decide +kernel

theorem g32p_supplierForest_actual_068636 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068636) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_068636
    g32p_supplierForest_actual_010542

def g32p_supplierForest_node_068664 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068664 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068664 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067325 := by
  decide +kernel

theorem g32p_supplierForest_actual_068664 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068664) ∧
        IsConj g (g32p_literalRepresentative 69) := by
  exact g32p_archive_step_lift _ _ 69 2 g32p_supplierForest_edge_068664
    g32p_supplierForest_actual_067325

def g32p_supplierForest_node_068667 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -2⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068667 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068667 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_065515 := by
  decide +kernel

theorem g32p_supplierForest_actual_068667 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068667) ∧
        IsConj g (g32p_literalRepresentative 7) := by
  exact g32p_archive_step_lift _ _ 7 1 g32p_supplierForest_edge_068667
    g32p_supplierForest_actual_065515

end HodgeLean.Foundations.Program

end
end
