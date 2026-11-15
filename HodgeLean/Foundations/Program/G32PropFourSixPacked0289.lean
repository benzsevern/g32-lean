import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0283
import HodgeLean.Foundations.Program.G32PropFourSixPacked0284
import HodgeLean.Foundations.Program.G32PropFourSixPacked0285
import HodgeLean.Foundations.Program.G32PropFourSixPacked0286
import HodgeLean.Foundations.Program.G32PropFourSixPacked0287
import HodgeLean.Foundations.Program.G32PropFourSixPacked0288

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_node_050154 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_050154 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_050154 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_053332 := by
  decide +kernel

theorem g32p_supplierForest_actual_050154 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_050154) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 2 g32p_supplierForest_edge_050154
    g32p_supplierForest_actual_053332

def g32p_supplierForest_node_050263 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_050263 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_050263 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_056317 := by
  decide +kernel

theorem g32p_supplierForest_actual_050263 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_050263) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_050263
    g32p_supplierForest_actual_056317

def g32p_supplierForest_node_050380 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_050380 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_050380 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_056695 := by
  decide +kernel

theorem g32p_supplierForest_actual_050380 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_050380) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_050380
    g32p_supplierForest_actual_056695

def g32p_supplierForest_node_050600 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_050600 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_050600 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_058862 := by
  decide +kernel

theorem g32p_supplierForest_actual_050600 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_050600) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_050600
    g32p_supplierForest_actual_058862

def g32p_supplierForest_node_050833 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_050833 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_050833 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_063217 := by
  decide +kernel

theorem g32p_supplierForest_actual_050833 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_050833) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_050833
    g32p_supplierForest_actual_063217

def g32p_supplierForest_node_051149 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051149 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051149 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069878 := by
  decide +kernel

theorem g32p_supplierForest_actual_051149 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051149) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_051149
    g32p_supplierForest_actual_069878

def g32p_supplierForest_node_051162 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051162 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051162 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059942 := by
  decide +kernel

theorem g32p_supplierForest_actual_051162 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051162) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_051162
    g32p_supplierForest_actual_059942

def g32p_supplierForest_node_051313 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_051313 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051313 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_058498 := by
  decide +kernel

theorem g32p_supplierForest_actual_051313 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051313) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_051313
    g32p_supplierForest_actual_058498

def g32p_supplierForest_node_051459 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_051459 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051459 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_052096 := by
  decide +kernel

theorem g32p_supplierForest_actual_051459 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051459) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_051459
    g32p_supplierForest_actual_052096

def g32p_supplierForest_node_051622 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_051622 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051622 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_050367 := by
  decide +kernel

theorem g32p_supplierForest_actual_051622 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051622) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_051622
    g32p_supplierForest_actual_050367

def g32p_supplierForest_node_051875 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_051875 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051875 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070353 := by
  decide +kernel

theorem g32p_supplierForest_actual_051875 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051875) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_051875
    g32p_supplierForest_actual_070353

def g32p_supplierForest_node_051989 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_051989 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_051989 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059165 := by
  decide +kernel

theorem g32p_supplierForest_actual_051989 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_051989) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_051989
    g32p_supplierForest_actual_059165

def g32p_supplierForest_node_052053 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_052053 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052053 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069221 := by
  decide +kernel

theorem g32p_supplierForest_actual_052053 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052053) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_052053
    g32p_supplierForest_actual_069221

def g32p_supplierForest_node_052175 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_052175 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052175 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056467 := by
  decide +kernel

theorem g32p_supplierForest_actual_052175 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052175) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_052175
    g32p_supplierForest_actual_056467

def g32p_supplierForest_node_052421 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052421 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062555 := by
  decide +kernel

theorem g32p_supplierForest_actual_052421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052421) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 0 g32p_supplierForest_edge_052421
    g32p_supplierForest_actual_062555

def g32p_supplierForest_node_052531 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_052531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052531 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063371 := by
  decide +kernel

theorem g32p_supplierForest_actual_052531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052531) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_052531
    g32p_supplierForest_actual_063371

def g32p_supplierForest_node_052736 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_052736 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052736 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_138578 := by
  decide +kernel

theorem g32p_supplierForest_actual_052736 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052736) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_052736
    g32p_supplierForest_actual_138578

def g32p_supplierForest_node_052967 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_052967 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_052967 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070129 := by
  decide +kernel

theorem g32p_supplierForest_actual_052967 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_052967) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_052967
    g32p_supplierForest_actual_070129

def g32p_supplierForest_node_053144 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_053144 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053144 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_128851 := by
  decide +kernel

theorem g32p_supplierForest_actual_053144 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053144) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053144
    g32p_supplierForest_actual_128851

def g32p_supplierForest_node_053194 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_053194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053194 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_056470 := by
  decide +kernel

theorem g32p_supplierForest_actual_053194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053194) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_053194
    g32p_supplierForest_actual_056470

def g32p_supplierForest_node_053292 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_053292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053292 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_055892 := by
  decide +kernel

theorem g32p_supplierForest_actual_053292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053292) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_053292
    g32p_supplierForest_actual_055892

def g32p_supplierForest_node_053408 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_053408 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053408 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060997 := by
  decide +kernel

theorem g32p_supplierForest_actual_053408 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053408) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_053408
    g32p_supplierForest_actual_060997

def g32p_supplierForest_node_053485 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_053485 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053485 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_052108 := by
  decide +kernel

theorem g32p_supplierForest_actual_053485 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053485) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053485
    g32p_supplierForest_actual_052108

def g32p_supplierForest_node_053832 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_053832 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053832 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131836 := by
  decide +kernel

theorem g32p_supplierForest_actual_053832 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053832) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_053832
    g32p_supplierForest_actual_131836

def g32p_supplierForest_node_053975 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_053975 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_053975 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_063792 := by
  decide +kernel

theorem g32p_supplierForest_actual_053975 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_053975) ∧
        IsConj g (g32p_literalRepresentative 43) := by
  exact g32p_archive_step_lift _ _ 43 1 g32p_supplierForest_edge_053975
    g32p_supplierForest_actual_063792

def g32p_supplierForest_node_054307 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_054307 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054307 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_047840 := by
  decide +kernel

theorem g32p_supplierForest_actual_054307 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054307) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 3 g32p_supplierForest_edge_054307
    g32p_supplierForest_actual_047840

def g32p_supplierForest_node_054435 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_054435 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054435 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_050250 := by
  decide +kernel

theorem g32p_supplierForest_actual_054435 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054435) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_054435
    g32p_supplierForest_actual_050250

def g32p_supplierForest_node_054536 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 2⟩, ⟨0, 1⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_054536 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054536 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_135193 := by
  decide +kernel

theorem g32p_supplierForest_actual_054536 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054536) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_054536
    g32p_supplierForest_actual_135193

def g32p_supplierForest_node_054592 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_054592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054592 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_049829 := by
  decide +kernel

theorem g32p_supplierForest_actual_054592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054592) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_054592
    g32p_supplierForest_actual_049829

def g32p_supplierForest_node_054754 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_054754 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_054754 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059153 := by
  decide +kernel

theorem g32p_supplierForest_actual_054754 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_054754) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_054754
    g32p_supplierForest_actual_059153

def g32p_supplierForest_node_055236 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_055236 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055236 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_058906 := by
  decide +kernel

theorem g32p_supplierForest_actual_055236 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055236) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_055236
    g32p_supplierForest_actual_058906

def g32p_supplierForest_node_055284 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_055284 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055284 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_060607 := by
  decide +kernel

theorem g32p_supplierForest_actual_055284 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055284) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_055284
    g32p_supplierForest_actual_060607

def g32p_supplierForest_node_055571 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_055571 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055571 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_054344 := by
  decide +kernel

theorem g32p_supplierForest_actual_055571 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055571) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_055571
    g32p_supplierForest_actual_054344

def g32p_supplierForest_node_055576 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_055576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055576 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063857 := by
  decide +kernel

theorem g32p_supplierForest_actual_055576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055576) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 3 g32p_supplierForest_edge_055576
    g32p_supplierForest_actual_063857

def g32p_supplierForest_node_055824 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_055824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_055824 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_050370 := by
  decide +kernel

theorem g32p_supplierForest_actual_055824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_055824) ∧
        IsConj g (g32p_literalRepresentative 39) := by
  exact g32p_archive_step_lift _ _ 39 3 g32p_supplierForest_edge_055824
    g32p_supplierForest_actual_050370

def g32p_supplierForest_node_056533 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_056533 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056533 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_138521 := by
  decide +kernel

theorem g32p_supplierForest_actual_056533 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056533) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_056533
    g32p_supplierForest_actual_138521

def g32p_supplierForest_node_056585 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_056585 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056585 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_137014 := by
  decide +kernel

theorem g32p_supplierForest_actual_056585 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056585) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_056585
    g32p_supplierForest_actual_137014

def g32p_supplierForest_node_056832 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_056832 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056832 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062070 := by
  decide +kernel

theorem g32p_supplierForest_actual_056832 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056832) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_056832
    g32p_supplierForest_actual_062070

def g32p_supplierForest_node_056855 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_056855 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_056855 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_054553 := by
  decide +kernel

theorem g32p_supplierForest_actual_056855 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_056855) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_056855
    g32p_supplierForest_actual_054553

def g32p_supplierForest_node_057059 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-2, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_057059 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057059 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_061220 := by
  decide +kernel

theorem g32p_supplierForest_actual_057059 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057059) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_057059
    g32p_supplierForest_actual_061220

def g32p_supplierForest_node_057880 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_057880 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_057880 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_133449 := by
  decide +kernel

theorem g32p_supplierForest_actual_057880 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_057880) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_057880
    g32p_supplierForest_actual_133449

def g32p_supplierForest_node_058240 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_058240 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058240 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_130626 := by
  decide +kernel

theorem g32p_supplierForest_actual_058240 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058240) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_058240
    g32p_supplierForest_actual_130626

def g32p_supplierForest_node_058326 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058326 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058326 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_059000 := by
  decide +kernel

theorem g32p_supplierForest_actual_058326 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058326) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_058326
    g32p_supplierForest_actual_059000

def g32p_supplierForest_node_058327 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058327 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058327 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_063699 := by
  decide +kernel

theorem g32p_supplierForest_actual_058327 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058327) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_058327
    g32p_supplierForest_actual_063699

def g32p_supplierForest_node_058830 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩]]

theorem g32p_supplierForest_edge_058830 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058830 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_069308 := by
  decide +kernel

theorem g32p_supplierForest_actual_058830 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058830) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_058830
    g32p_supplierForest_actual_069308

def g32p_supplierForest_node_058865 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_058865 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_058865 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_060216 := by
  decide +kernel

theorem g32p_supplierForest_actual_058865 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_058865) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_058865
    g32p_supplierForest_actual_060216

def g32p_supplierForest_node_059227 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059227 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059227 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_137498 := by
  decide +kernel

theorem g32p_supplierForest_actual_059227 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059227) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_059227
    g32p_supplierForest_actual_137498

def g32p_supplierForest_node_059314 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_059314 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059314 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_138665 := by
  decide +kernel

theorem g32p_supplierForest_actual_059314 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059314) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_059314
    g32p_supplierForest_actual_138665

def g32p_supplierForest_node_059341 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059341 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059341 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_059853 := by
  decide +kernel

theorem g32p_supplierForest_actual_059341 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059341) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_059341
    g32p_supplierForest_actual_059853

def g32p_supplierForest_node_059428 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_059428 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059428 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_062567 := by
  decide +kernel

theorem g32p_supplierForest_actual_059428 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059428) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_059428
    g32p_supplierForest_actual_062567

def g32p_supplierForest_node_059706 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059706 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067166 := by
  decide +kernel

theorem g32p_supplierForest_actual_059706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059706) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_059706
    g32p_supplierForest_actual_067166

def g32p_supplierForest_node_059732 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_059732 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059732 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_064665 := by
  decide +kernel

theorem g32p_supplierForest_actual_059732 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059732) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_059732
    g32p_supplierForest_actual_064665

def g32p_supplierForest_node_059778 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_059778 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059778 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131750 := by
  decide +kernel

theorem g32p_supplierForest_actual_059778 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059778) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_059778
    g32p_supplierForest_actual_131750

def g32p_supplierForest_node_059958 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_059958 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_059958 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011182 := by
  decide +kernel

theorem g32p_supplierForest_actual_059958 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_059958) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_059958
    g32p_supplierForest_actual_011182

def g32p_supplierForest_node_060035 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_060035 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060035 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071184 := by
  decide +kernel

theorem g32p_supplierForest_actual_060035 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060035) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_060035
    g32p_supplierForest_actual_071184

def g32p_supplierForest_node_060319 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060319 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060319 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_011811 := by
  decide +kernel

theorem g32p_supplierForest_actual_060319 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060319) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_060319
    g32p_supplierForest_actual_011811

def g32p_supplierForest_node_060531 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060531 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060531 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_139576 := by
  decide +kernel

theorem g32p_supplierForest_actual_060531 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060531) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_060531
    g32p_supplierForest_actual_139576

def g32p_supplierForest_node_060988 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_060988 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_060988 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051833 := by
  decide +kernel

theorem g32p_supplierForest_actual_060988 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_060988) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_060988
    g32p_supplierForest_actual_051833

def g32p_supplierForest_node_061339 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_061339 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061339 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062924 := by
  decide +kernel

theorem g32p_supplierForest_actual_061339 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061339) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_061339
    g32p_supplierForest_actual_062924

def g32p_supplierForest_node_061371 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061371 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061371 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_063003 := by
  decide +kernel

theorem g32p_supplierForest_actual_061371 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061371) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_061371
    g32p_supplierForest_actual_063003

def g32p_supplierForest_node_061405 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 1⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061405 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061405 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061406 := by
  decide +kernel

theorem g32p_supplierForest_actual_061405 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061405) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_061405
    g32p_supplierForest_actual_061406

def g32p_supplierForest_node_061468 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061468 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061468 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_062892 := by
  decide +kernel

theorem g32p_supplierForest_actual_061468 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061468) ∧
        IsConj g (g32p_literalRepresentative 72) := by
  exact g32p_archive_step_lift _ _ 72 2 g32p_supplierForest_edge_061468
    g32p_supplierForest_actual_062892

def g32p_supplierForest_node_061580 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨2, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_061580 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061580 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_128852 := by
  decide +kernel

theorem g32p_supplierForest_actual_061580 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061580) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 0 g32p_supplierForest_edge_061580
    g32p_supplierForest_actual_128852

def g32p_supplierForest_node_061630 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061630 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061630 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068117 := by
  decide +kernel

theorem g32p_supplierForest_actual_061630 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061630) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_061630
    g32p_supplierForest_actual_068117

def g32p_supplierForest_node_061638 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-2, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061638 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061638 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_051294 := by
  decide +kernel

theorem g32p_supplierForest_actual_061638 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061638) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_061638
    g32p_supplierForest_actual_051294

def g32p_supplierForest_node_061670 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061670 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061670 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_050710 := by
  decide +kernel

theorem g32p_supplierForest_actual_061670 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061670) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 1 g32p_supplierForest_edge_061670
    g32p_supplierForest_actual_050710

def g32p_supplierForest_node_061709 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061709 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061709 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_071002 := by
  decide +kernel

theorem g32p_supplierForest_actual_061709 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061709) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_061709
    g32p_supplierForest_actual_071002

def g32p_supplierForest_node_061716 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_061716 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061716 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049698 := by
  decide +kernel

theorem g32p_supplierForest_actual_061716 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061716) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_061716
    g32p_supplierForest_actual_049698

def g32p_supplierForest_node_061784 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_061784 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061784 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_044612 := by
  decide +kernel

theorem g32p_supplierForest_actual_061784 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061784) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_061784
    g32p_supplierForest_actual_044612

def g32p_supplierForest_node_061978 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_061978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_061978 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_051196 := by
  decide +kernel

theorem g32p_supplierForest_actual_061978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_061978) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_061978
    g32p_supplierForest_actual_051196

def g32p_supplierForest_node_062440 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_062440 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062440 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_059147 := by
  decide +kernel

theorem g32p_supplierForest_actual_062440 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062440) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 1 g32p_supplierForest_edge_062440
    g32p_supplierForest_actual_059147

def g32p_supplierForest_node_062566 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062566 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_129757 := by
  decide +kernel

theorem g32p_supplierForest_actual_062566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062566) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_062566
    g32p_supplierForest_actual_129757

def g32p_supplierForest_node_062742 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_062742 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062742 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_066907 := by
  decide +kernel

theorem g32p_supplierForest_actual_062742 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062742) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_062742
    g32p_supplierForest_actual_066907

def g32p_supplierForest_node_062896 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_062896 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_062896 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_142236 := by
  decide +kernel

theorem g32p_supplierForest_actual_062896 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_062896) ∧
        IsConj g (g32p_literalRepresentative 20) := by
  exact g32p_archive_step_lift _ _ 20 2 g32p_supplierForest_edge_062896
    g32p_supplierForest_actual_142236

def g32p_supplierForest_node_063016 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063016 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_052767 := by
  decide +kernel

theorem g32p_supplierForest_actual_063016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063016) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 0 g32p_supplierForest_edge_063016
    g32p_supplierForest_actual_052767

def g32p_supplierForest_node_063119 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063119 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063119 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130295 := by
  decide +kernel

theorem g32p_supplierForest_actual_063119 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063119) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063119
    g32p_supplierForest_actual_130295

def g32p_supplierForest_node_063171 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_063171 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063171 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_061356 := by
  decide +kernel

theorem g32p_supplierForest_actual_063171 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063171) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 2 g32p_supplierForest_edge_063171
    g32p_supplierForest_actual_061356

def g32p_supplierForest_node_063174 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063174 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_066100 := by
  decide +kernel

theorem g32p_supplierForest_actual_063174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063174) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_063174
    g32p_supplierForest_actual_066100

def g32p_supplierForest_node_063465 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_063465 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063465 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064284 := by
  decide +kernel

theorem g32p_supplierForest_actual_063465 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063465) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_063465
    g32p_supplierForest_actual_064284

def g32p_supplierForest_node_063557 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨2, 0⟩, ⟨2, 2⟩, ⟨2, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_063557 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_063557 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_070630 := by
  decide +kernel

theorem g32p_supplierForest_actual_063557 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_063557) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_063557
    g32p_supplierForest_actual_070630

def g32p_supplierForest_node_064004 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064004 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064004 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_059971 := by
  decide +kernel

theorem g32p_supplierForest_actual_064004 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064004) ∧
        IsConj g (g32p_literalRepresentative 41) := by
  exact g32p_archive_step_lift _ _ 41 0 g32p_supplierForest_edge_064004
    g32p_supplierForest_actual_059971

def g32p_supplierForest_node_064176 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_064176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064176 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_055665 := by
  decide +kernel

theorem g32p_supplierForest_actual_064176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064176) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_064176
    g32p_supplierForest_actual_055665

def g32p_supplierForest_node_064231 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064231 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064231 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_130381 := by
  decide +kernel

theorem g32p_supplierForest_actual_064231 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064231) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 0 g32p_supplierForest_edge_064231
    g32p_supplierForest_actual_130381

def g32p_supplierForest_node_064621 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_064621 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064621 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_047880 := by
  decide +kernel

theorem g32p_supplierForest_actual_064621 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064621) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_064621
    g32p_supplierForest_actual_047880

def g32p_supplierForest_node_064810 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -2⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_064810 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064810 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_133045 := by
  decide +kernel

theorem g32p_supplierForest_actual_064810 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064810) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064810
    g32p_supplierForest_actual_133045

def g32p_supplierForest_node_064909 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_064909 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_064909 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067179 := by
  decide +kernel

theorem g32p_supplierForest_actual_064909 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_064909) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_064909
    g32p_supplierForest_actual_067179

def g32p_supplierForest_node_065364 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_065364 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065364 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064888 := by
  decide +kernel

theorem g32p_supplierForest_actual_065364 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065364) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_065364
    g32p_supplierForest_actual_064888

def g32p_supplierForest_node_065860 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_065860 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065860 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_131368 := by
  decide +kernel

theorem g32p_supplierForest_actual_065860 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065860) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_065860
    g32p_supplierForest_actual_131368

def g32p_supplierForest_node_065996 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 2⟩, ⟨1, 2⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_065996 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_065996 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_128129 := by
  decide +kernel

theorem g32p_supplierForest_actual_065996 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_065996) ∧
        IsConj g (g32p_literalRepresentative 68) := by
  exact g32p_archive_step_lift _ _ 68 3 g32p_supplierForest_edge_065996
    g32p_supplierForest_actual_128129

def g32p_supplierForest_node_066288 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_066288 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066288 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_062576 := by
  decide +kernel

theorem g32p_supplierForest_actual_066288 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066288) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_066288
    g32p_supplierForest_actual_062576

def g32p_supplierForest_node_066456 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_066456 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_066456 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_133168 := by
  decide +kernel

theorem g32p_supplierForest_actual_066456 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_066456) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_066456
    g32p_supplierForest_actual_133168

def g32p_supplierForest_node_067095 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_067095 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067095 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_055550 := by
  decide +kernel

theorem g32p_supplierForest_actual_067095 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067095) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067095
    g32p_supplierForest_actual_055550

def g32p_supplierForest_node_067346 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067346 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067346 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_069113 := by
  decide +kernel

theorem g32p_supplierForest_actual_067346 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067346) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_067346
    g32p_supplierForest_actual_069113

def g32p_supplierForest_node_067566 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067566 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067566 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_128417 := by
  decide +kernel

theorem g32p_supplierForest_actual_067566 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067566) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_067566
    g32p_supplierForest_actual_128417

def g32p_supplierForest_node_067684 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 2⟩, ⟨2, 2⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_067684 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067684 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_053378 := by
  decide +kernel

theorem g32p_supplierForest_actual_067684 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067684) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 0 g32p_supplierForest_edge_067684
    g32p_supplierForest_actual_053378

def g32p_supplierForest_node_067773 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_067773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_067773 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_049700 := by
  decide +kernel

theorem g32p_supplierForest_actual_067773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_067773) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 1 g32p_supplierForest_edge_067773
    g32p_supplierForest_actual_049700

def g32p_supplierForest_node_068159 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_068159 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068159 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064521 := by
  decide +kernel

theorem g32p_supplierForest_actual_068159 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068159) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_068159
    g32p_supplierForest_actual_064521

def g32p_supplierForest_node_068167 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068167 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068167 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_048481 := by
  decide +kernel

theorem g32p_supplierForest_actual_068167 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068167) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_068167
    g32p_supplierForest_actual_048481

def g32p_supplierForest_node_068173 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩, ⟨-2, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_068173 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068173 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064549 := by
  decide +kernel

theorem g32p_supplierForest_actual_068173 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068173) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_068173
    g32p_supplierForest_actual_064549

def g32p_supplierForest_node_068188 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-2, -2⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_068188 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068188 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064580 := by
  decide +kernel

theorem g32p_supplierForest_actual_068188 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068188) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_068188
    g32p_supplierForest_actual_064580

def g32p_supplierForest_node_068368 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_068368 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068368 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_071366 := by
  decide +kernel

theorem g32p_supplierForest_actual_068368 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068368) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068368
    g32p_supplierForest_actual_071366

def g32p_supplierForest_node_068370 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_068370 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068370 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_052290 := by
  decide +kernel

theorem g32p_supplierForest_actual_068370 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068370) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_068370
    g32p_supplierForest_actual_052290

def g32p_supplierForest_node_068432 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068432 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068432 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_129328 := by
  decide +kernel

theorem g32p_supplierForest_actual_068432 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068432) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_068432
    g32p_supplierForest_actual_129328

def g32p_supplierForest_node_068524 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_068524 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068524 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_134937 := by
  decide +kernel

theorem g32p_supplierForest_actual_068524 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068524) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 0 g32p_supplierForest_edge_068524
    g32p_supplierForest_actual_134937

def g32p_supplierForest_node_068706 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068706 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068706 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067447 := by
  decide +kernel

theorem g32p_supplierForest_actual_068706 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068706) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_068706
    g32p_supplierForest_actual_067447

def g32p_supplierForest_node_068834 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_068834 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_068834 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_067809 := by
  decide +kernel

theorem g32p_supplierForest_actual_068834 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_068834) ∧
        IsConj g (g32p_literalRepresentative 22) := by
  exact g32p_archive_step_lift _ _ 22 2 g32p_supplierForest_edge_068834
    g32p_supplierForest_actual_067809

def g32p_supplierForest_node_069017 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 1⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩]]

theorem g32p_supplierForest_edge_069017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069017 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_068513 := by
  decide +kernel

theorem g32p_supplierForest_actual_069017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069017) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_069017
    g32p_supplierForest_actual_068513

def g32p_supplierForest_node_069077 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069077 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069077 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_064997 := by
  decide +kernel

theorem g32p_supplierForest_actual_069077 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069077) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 2 g32p_supplierForest_edge_069077
    g32p_supplierForest_actual_064997

def g32p_supplierForest_node_069282 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069282 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_057773 := by
  decide +kernel

theorem g32p_supplierForest_actual_069282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069282) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_069282
    g32p_supplierForest_actual_057773

def g32p_supplierForest_node_069415 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_069415 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069415 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070123 := by
  decide +kernel

theorem g32p_supplierForest_actual_069415 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069415) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 2 g32p_supplierForest_edge_069415
    g32p_supplierForest_actual_070123

def g32p_supplierForest_node_069504 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_069504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069504 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_070380 := by
  decide +kernel

theorem g32p_supplierForest_actual_069504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069504) ∧
        IsConj g (g32p_literalRepresentative 70) := by
  exact g32p_archive_step_lift _ _ 70 2 g32p_supplierForest_edge_069504
    g32p_supplierForest_actual_070380

def g32p_supplierForest_node_069620 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-2, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_069620 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_069620 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_130699 := by
  decide +kernel

theorem g32p_supplierForest_actual_069620 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_069620) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_069620
    g32p_supplierForest_actual_130699

def g32p_supplierForest_node_070051 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_070051 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070051 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_071540 := by
  decide +kernel

theorem g32p_supplierForest_actual_070051 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070051) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_070051
    g32p_supplierForest_actual_071540

def g32p_supplierForest_node_070445 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070445 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070445 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_048856 := by
  decide +kernel

theorem g32p_supplierForest_actual_070445 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070445) ∧
        IsConj g (g32p_literalRepresentative 21) := by
  exact g32p_archive_step_lift _ _ 21 3 g32p_supplierForest_edge_070445
    g32p_supplierForest_actual_048856

def g32p_supplierForest_node_070496 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_070496 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070496 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_049043 := by
  decide +kernel

theorem g32p_supplierForest_actual_070496 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070496) ∧
        IsConj g (g32p_literalRepresentative 38) := by
  exact g32p_archive_step_lift _ _ 38 3 g32p_supplierForest_edge_070496
    g32p_supplierForest_actual_049043

def g32p_supplierForest_node_070618 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, -2⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_070618 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070618 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_142894 := by
  decide +kernel

theorem g32p_supplierForest_actual_070618 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070618) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 2 g32p_supplierForest_edge_070618
    g32p_supplierForest_actual_142894

def g32p_supplierForest_node_070928 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_070928 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070928 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_135807 := by
  decide +kernel

theorem g32p_supplierForest_actual_070928 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070928) ∧
        IsConj g (g32p_literalRepresentative 73) := by
  exact g32p_archive_step_lift _ _ 73 0 g32p_supplierForest_edge_070928
    g32p_supplierForest_actual_135807

def g32p_supplierForest_node_070996 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 2⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩]]

theorem g32p_supplierForest_edge_070996 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_070996 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_134390 := by
  decide +kernel

theorem g32p_supplierForest_actual_070996 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_070996) ∧
        IsConj g (g32p_literalRepresentative 42) := by
  exact g32p_archive_step_lift _ _ 42 2 g32p_supplierForest_edge_070996
    g32p_supplierForest_actual_134390

def g32p_supplierForest_node_071867 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_071867 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071867 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081588 := by
  decide +kernel

theorem g32p_supplierForest_actual_071867 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071867) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_071867
    g32p_supplierForest_actual_081588

def g32p_supplierForest_node_071877 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_071877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071877 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093843 := by
  decide +kernel

theorem g32p_supplierForest_actual_071877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071877) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_071877
    g32p_supplierForest_actual_093843

def g32p_supplierForest_node_071945 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_071945 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071945 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_015384 := by
  decide +kernel

theorem g32p_supplierForest_actual_071945 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071945) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_071945
    g32p_supplierForest_actual_015384

def g32p_supplierForest_node_071978 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_071978 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_071978 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072504 := by
  decide +kernel

theorem g32p_supplierForest_actual_071978 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_071978) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_071978
    g32p_supplierForest_actual_072504

def g32p_supplierForest_node_072105 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_072105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072105 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081915 := by
  decide +kernel

theorem g32p_supplierForest_actual_072105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072105) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072105
    g32p_supplierForest_actual_081915

def g32p_supplierForest_node_072628 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_072628 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_072628 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082611 := by
  decide +kernel

theorem g32p_supplierForest_actual_072628 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_072628) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_072628
    g32p_supplierForest_actual_082611

def g32p_supplierForest_node_073023 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_073023 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073023 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_100538 := by
  decide +kernel

theorem g32p_supplierForest_actual_073023 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073023) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_073023
    g32p_supplierForest_actual_100538

def g32p_supplierForest_node_073215 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_073215 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073215 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_079500 := by
  decide +kernel

theorem g32p_supplierForest_actual_073215 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073215) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073215
    g32p_supplierForest_actual_079500

def g32p_supplierForest_node_073291 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-2, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_073291 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073291 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_083440 := by
  decide +kernel

theorem g32p_supplierForest_actual_073291 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073291) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_073291
    g32p_supplierForest_actual_083440

def g32p_supplierForest_node_073491 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073491 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073491 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_093523 := by
  decide +kernel

theorem g32p_supplierForest_actual_073491 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073491) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_073491
    g32p_supplierForest_actual_093523

def g32p_supplierForest_node_073637 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -2⟩, ⟨1, -1⟩, ⟨-1, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073637 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073637 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_081555 := by
  decide +kernel

theorem g32p_supplierForest_actual_073637 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073637) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_073637
    g32p_supplierForest_actual_081555

def g32p_supplierForest_node_073789 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_073789 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_073789 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072370 := by
  decide +kernel

theorem g32p_supplierForest_actual_073789 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_073789) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_073789
    g32p_supplierForest_actual_072370

def g32p_supplierForest_node_074230 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 2⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_074230 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074230 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_075229 := by
  decide +kernel

theorem g32p_supplierForest_actual_074230 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074230) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_074230
    g32p_supplierForest_actual_075229

def g32p_supplierForest_node_074299 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_074299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074299 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073734 := by
  decide +kernel

theorem g32p_supplierForest_actual_074299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074299) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_074299
    g32p_supplierForest_actual_073734

def g32p_supplierForest_node_074355 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 0⟩, ⟨1, 0⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_074355 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_074355 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073118 := by
  decide +kernel

theorem g32p_supplierForest_actual_074355 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_074355) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_074355
    g32p_supplierForest_actual_073118

def g32p_supplierForest_node_075105 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_075105 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075105 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_079492 := by
  decide +kernel

theorem g32p_supplierForest_actual_075105 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075105) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_075105
    g32p_supplierForest_actual_079492

def g32p_supplierForest_node_075116 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075116 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075116 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085024 := by
  decide +kernel

theorem g32p_supplierForest_actual_075116 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075116) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_075116
    g32p_supplierForest_actual_085024

def g32p_supplierForest_node_075270 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -2⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075270 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075270 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087211 := by
  decide +kernel

theorem g32p_supplierForest_actual_075270 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075270) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_075270
    g32p_supplierForest_actual_087211

def g32p_supplierForest_node_075568 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075568 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075568 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075701 := by
  decide +kernel

theorem g32p_supplierForest_actual_075568 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075568) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_075568
    g32p_supplierForest_actual_075701

def g32p_supplierForest_node_075613 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075613 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075613 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_145030 := by
  decide +kernel

theorem g32p_supplierForest_actual_075613 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075613) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_075613
    g32p_supplierForest_actual_145030

def g32p_supplierForest_node_075740 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_075740 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075740 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_084830 := by
  decide +kernel

theorem g32p_supplierForest_actual_075740 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075740) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_075740
    g32p_supplierForest_actual_084830

def g32p_supplierForest_node_075759 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_075759 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075759 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_077366 := by
  decide +kernel

theorem g32p_supplierForest_actual_075759 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075759) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_075759
    g32p_supplierForest_actual_077366

def g32p_supplierForest_node_075770 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_075770 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075770 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_072077 := by
  decide +kernel

theorem g32p_supplierForest_actual_075770 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075770) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_075770
    g32p_supplierForest_actual_072077

def g32p_supplierForest_node_075791 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_075791 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075791 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_095480 := by
  decide +kernel

theorem g32p_supplierForest_actual_075791 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075791) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_075791
    g32p_supplierForest_actual_095480

def g32p_supplierForest_node_075914 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_075914 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_075914 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_072301 := by
  decide +kernel

theorem g32p_supplierForest_actual_075914 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_075914) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_075914
    g32p_supplierForest_actual_072301

def g32p_supplierForest_node_076083 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076083 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076083 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076039 := by
  decide +kernel

theorem g32p_supplierForest_actual_076083 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076083) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_076083
    g32p_supplierForest_actual_076039

def g32p_supplierForest_node_076168 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076168 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076168 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084310 := by
  decide +kernel

theorem g32p_supplierForest_actual_076168 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076168) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_076168
    g32p_supplierForest_actual_084310

def g32p_supplierForest_node_076176 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076176 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076176 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_101005 := by
  decide +kernel

theorem g32p_supplierForest_actual_076176 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076176) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_076176
    g32p_supplierForest_actual_101005

def g32p_supplierForest_node_076282 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_076282 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076282 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075539 := by
  decide +kernel

theorem g32p_supplierForest_actual_076282 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076282) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_076282
    g32p_supplierForest_actual_075539

def g32p_supplierForest_node_076507 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_076507 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076507 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_089661 := by
  decide +kernel

theorem g32p_supplierForest_actual_076507 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076507) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 3 g32p_supplierForest_edge_076507
    g32p_supplierForest_actual_089661

def g32p_supplierForest_node_076517 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_076517 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076517 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081459 := by
  decide +kernel

theorem g32p_supplierForest_actual_076517 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076517) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_076517
    g32p_supplierForest_actual_081459

def g32p_supplierForest_node_076657 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_076657 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076657 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082464 := by
  decide +kernel

theorem g32p_supplierForest_actual_076657 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076657) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_076657
    g32p_supplierForest_actual_082464

def g32p_supplierForest_node_076774 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_076774 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_076774 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_085593 := by
  decide +kernel

theorem g32p_supplierForest_actual_076774 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_076774) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_076774
    g32p_supplierForest_actual_085593

def g32p_supplierForest_node_077065 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨2, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077065 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077065 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_078797 := by
  decide +kernel

theorem g32p_supplierForest_actual_077065 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077065) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_077065
    g32p_supplierForest_actual_078797

def g32p_supplierForest_node_077217 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077217 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077217 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_076044 := by
  decide +kernel

theorem g32p_supplierForest_actual_077217 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077217) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_077217
    g32p_supplierForest_actual_076044

def g32p_supplierForest_node_077483 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077483 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077483 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_073147 := by
  decide +kernel

theorem g32p_supplierForest_actual_077483 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077483) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_077483
    g32p_supplierForest_actual_073147

def g32p_supplierForest_node_077641 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077641 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077641 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077634 := by
  decide +kernel

theorem g32p_supplierForest_actual_077641 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077641) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_077641
    g32p_supplierForest_actual_077634

def g32p_supplierForest_node_077645 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077645 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077645 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_149254 := by
  decide +kernel

theorem g32p_supplierForest_actual_077645 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077645) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_077645
    g32p_supplierForest_actual_149254

def g32p_supplierForest_node_077714 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077714 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077714 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_094695 := by
  decide +kernel

theorem g32p_supplierForest_actual_077714 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077714) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_077714
    g32p_supplierForest_actual_094695

def g32p_supplierForest_node_077737 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨2, 1⟩, ⟨2, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_077737 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077737 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_090704 := by
  decide +kernel

theorem g32p_supplierForest_actual_077737 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077737) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 3 g32p_supplierForest_edge_077737
    g32p_supplierForest_actual_090704

def g32p_supplierForest_node_077769 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077769 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_016542 := by
  decide +kernel

theorem g32p_supplierForest_actual_077769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077769) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_077769
    g32p_supplierForest_actual_016542

def g32p_supplierForest_node_077795 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_077795 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077795 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073571 := by
  decide +kernel

theorem g32p_supplierForest_actual_077795 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077795) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_077795
    g32p_supplierForest_actual_073571

def g32p_supplierForest_node_077880 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_077880 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077880 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076435 := by
  decide +kernel

theorem g32p_supplierForest_actual_077880 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077880) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 3 g32p_supplierForest_edge_077880
    g32p_supplierForest_actual_076435

def g32p_supplierForest_node_077998 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_077998 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_077998 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_017536 := by
  decide +kernel

theorem g32p_supplierForest_actual_077998 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_077998) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_077998
    g32p_supplierForest_actual_017536

def g32p_supplierForest_node_078073 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩, ⟨-2, -2⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩]]

theorem g32p_supplierForest_edge_078073 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078073 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_075084 := by
  decide +kernel

theorem g32p_supplierForest_actual_078073 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078073) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_078073
    g32p_supplierForest_actual_075084

def g32p_supplierForest_node_078522 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078522 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078522 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_077662 := by
  decide +kernel

theorem g32p_supplierForest_actual_078522 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078522) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_078522
    g32p_supplierForest_actual_077662

def g32p_supplierForest_node_078666 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_078666 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078666 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_093471 := by
  decide +kernel

theorem g32p_supplierForest_actual_078666 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078666) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_078666
    g32p_supplierForest_actual_093471

def g32p_supplierForest_node_078729 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 2⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_078729 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078729 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023308 := by
  decide +kernel

theorem g32p_supplierForest_actual_078729 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078729) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_078729
    g32p_supplierForest_actual_023308

def g32p_supplierForest_node_078785 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_078785 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078785 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_097356 := by
  decide +kernel

theorem g32p_supplierForest_actual_078785 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078785) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_078785
    g32p_supplierForest_actual_097356

def g32p_supplierForest_node_078935 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩], ![⟨2, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_078935 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_078935 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020849 := by
  decide +kernel

theorem g32p_supplierForest_actual_078935 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_078935) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_078935
    g32p_supplierForest_actual_020849

def g32p_supplierForest_node_079151 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -2⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_079151 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079151 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_020306 := by
  decide +kernel

theorem g32p_supplierForest_actual_079151 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079151) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_079151
    g32p_supplierForest_actual_020306

def g32p_supplierForest_node_079194 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079194 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079194 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_086769 := by
  decide +kernel

theorem g32p_supplierForest_actual_079194 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079194) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_079194
    g32p_supplierForest_actual_086769

def g32p_supplierForest_node_079219 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨2, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079219 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079219 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_086807 := by
  decide +kernel

theorem g32p_supplierForest_actual_079219 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079219) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_079219
    g32p_supplierForest_actual_086807

def g32p_supplierForest_node_079224 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨2, 2⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_079224 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079224 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_090907 := by
  decide +kernel

theorem g32p_supplierForest_actual_079224 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079224) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_079224
    g32p_supplierForest_actual_090907

def g32p_supplierForest_node_079269 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079269 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079269 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_079810 := by
  decide +kernel

theorem g32p_supplierForest_actual_079269 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079269) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_079269
    g32p_supplierForest_actual_079810

def g32p_supplierForest_node_079361 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_079361 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079361 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080356 := by
  decide +kernel

theorem g32p_supplierForest_actual_079361 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079361) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_079361
    g32p_supplierForest_actual_080356

def g32p_supplierForest_node_079439 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨2, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_079439 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079439 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090524 := by
  decide +kernel

theorem g32p_supplierForest_actual_079439 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079439) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_079439
    g32p_supplierForest_actual_090524

def g32p_supplierForest_node_079466 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩, ⟨-2, -1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_079466 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079466 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_080553 := by
  decide +kernel

theorem g32p_supplierForest_actual_079466 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079466) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_079466
    g32p_supplierForest_actual_080553

def g32p_supplierForest_node_079491 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, 0⟩], ![⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_079491 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079491 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096057 := by
  decide +kernel

theorem g32p_supplierForest_actual_079491 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079491) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_079491
    g32p_supplierForest_actual_096057

def g32p_supplierForest_node_079498 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_079498 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079498 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090069 := by
  decide +kernel

theorem g32p_supplierForest_actual_079498 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079498) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_079498
    g32p_supplierForest_actual_090069

def g32p_supplierForest_node_079547 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨2, 2⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_079547 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_079547 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_073147 := by
  decide +kernel

theorem g32p_supplierForest_actual_079547 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_079547) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_079547
    g32p_supplierForest_actual_073147

def g32p_supplierForest_node_080053 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨-1, -2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080053 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080053 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_088267 := by
  decide +kernel

theorem g32p_supplierForest_actual_080053 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080053) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_080053
    g32p_supplierForest_actual_088267

def g32p_supplierForest_node_080163 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨0, 1⟩, ⟨1, 2⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, -1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_080163 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080163 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_080683 := by
  decide +kernel

theorem g32p_supplierForest_actual_080163 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080163) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_080163
    g32p_supplierForest_actual_080683

def g32p_supplierForest_node_080166 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_080166 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080166 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_089165 := by
  decide +kernel

theorem g32p_supplierForest_actual_080166 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080166) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_080166
    g32p_supplierForest_actual_089165

def g32p_supplierForest_node_080184 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_080184 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080184 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_078899 := by
  decide +kernel

theorem g32p_supplierForest_actual_080184 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080184) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_080184
    g32p_supplierForest_actual_078899

def g32p_supplierForest_node_080299 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080299 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080299 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_016421 := by
  decide +kernel

theorem g32p_supplierForest_actual_080299 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080299) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_080299
    g32p_supplierForest_actual_016421

def g32p_supplierForest_node_080333 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_080333 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080333 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084246 := by
  decide +kernel

theorem g32p_supplierForest_actual_080333 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080333) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_080333
    g32p_supplierForest_actual_084246

def g32p_supplierForest_node_080421 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080421 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080421 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_093484 := by
  decide +kernel

theorem g32p_supplierForest_actual_080421 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080421) ∧
        IsConj g (g32p_literalRepresentative 53) := by
  exact g32p_archive_step_lift _ _ 53 2 g32p_supplierForest_edge_080421
    g32p_supplierForest_actual_093484

def g32p_supplierForest_node_080425 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, -1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_080425 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080425 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077767 := by
  decide +kernel

theorem g32p_supplierForest_actual_080425 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080425) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_080425
    g32p_supplierForest_actual_077767

def g32p_supplierForest_node_080504 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨2, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_080504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080504 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091612 := by
  decide +kernel

theorem g32p_supplierForest_actual_080504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080504) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_080504
    g32p_supplierForest_actual_091612

def g32p_supplierForest_node_080563 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_080563 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080563 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021864 := by
  decide +kernel

theorem g32p_supplierForest_actual_080563 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080563) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_080563
    g32p_supplierForest_actual_021864

def g32p_supplierForest_node_080595 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080595 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080595 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_078045 := by
  decide +kernel

theorem g32p_supplierForest_actual_080595 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080595) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_080595
    g32p_supplierForest_actual_078045

def g32p_supplierForest_node_080649 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_080649 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080649 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_072338 := by
  decide +kernel

theorem g32p_supplierForest_actual_080649 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080649) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_080649
    g32p_supplierForest_actual_072338

def g32p_supplierForest_node_080686 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩, ⟨1, 2⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_080686 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080686 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_017650 := by
  decide +kernel

theorem g32p_supplierForest_actual_080686 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080686) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_080686
    g32p_supplierForest_actual_017650

def g32p_supplierForest_node_080773 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_080773 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080773 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_096769 := by
  decide +kernel

theorem g32p_supplierForest_actual_080773 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080773) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_080773
    g32p_supplierForest_actual_096769

def g32p_supplierForest_node_080824 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080824 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080824 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091966 := by
  decide +kernel

theorem g32p_supplierForest_actual_080824 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080824) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_080824
    g32p_supplierForest_actual_091966

def g32p_supplierForest_node_080879 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_080879 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080879 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_092004 := by
  decide +kernel

theorem g32p_supplierForest_actual_080879 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080879) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_080879
    g32p_supplierForest_actual_092004

def g32p_supplierForest_node_080962 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_080962 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_080962 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_078581 := by
  decide +kernel

theorem g32p_supplierForest_actual_080962 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_080962) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_080962
    g32p_supplierForest_actual_078581

def g32p_supplierForest_node_081016 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 2⟩, ⟨1, 2⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_081016 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081016 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_099204 := by
  decide +kernel

theorem g32p_supplierForest_actual_081016 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081016) ∧
        IsConj g (g32p_literalRepresentative 54) := by
  exact g32p_archive_step_lift _ _ 54 1 g32p_supplierForest_edge_081016
    g32p_supplierForest_actual_099204

def g32p_supplierForest_node_081033 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_081033 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081033 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_018422 := by
  decide +kernel

theorem g32p_supplierForest_actual_081033 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081033) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_081033
    g32p_supplierForest_actual_018422

def g32p_supplierForest_node_081103 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081103 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081103 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_076275 := by
  decide +kernel

theorem g32p_supplierForest_actual_081103 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081103) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_081103
    g32p_supplierForest_actual_076275

def g32p_supplierForest_node_081378 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081378 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081378 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022113 := by
  decide +kernel

theorem g32p_supplierForest_actual_081378 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081378) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_081378
    g32p_supplierForest_actual_022113

def g32p_supplierForest_node_081593 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩], ![⟨0, -2⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_081593 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_081593 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076696 := by
  decide +kernel

theorem g32p_supplierForest_actual_081593 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_081593) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_081593
    g32p_supplierForest_actual_076696

def g32p_supplierForest_node_082292 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_082292 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082292 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099289 := by
  decide +kernel

theorem g32p_supplierForest_actual_082292 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082292) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_082292
    g32p_supplierForest_actual_099289

def g32p_supplierForest_node_082713 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, 2⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_082713 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_082713 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_076412 := by
  decide +kernel

theorem g32p_supplierForest_actual_082713 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_082713) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_082713
    g32p_supplierForest_actual_076412

def g32p_supplierForest_node_083423 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 1⟩, ⟨2, 0⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_083423 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083423 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_086432 := by
  decide +kernel

theorem g32p_supplierForest_actual_083423 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083423) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_083423
    g32p_supplierForest_actual_086432

def g32p_supplierForest_node_083682 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_083682 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_083682 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088044 := by
  decide +kernel

theorem g32p_supplierForest_actual_083682 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_083682) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_083682
    g32p_supplierForest_actual_088044

def g32p_supplierForest_node_084018 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084018 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084018 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_022661 := by
  decide +kernel

theorem g32p_supplierForest_actual_084018 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084018) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_084018
    g32p_supplierForest_actual_022661

def g32p_supplierForest_node_084038 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨1, 1⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_084038 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084038 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_092931 := by
  decide +kernel

theorem g32p_supplierForest_actual_084038 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084038) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084038
    g32p_supplierForest_actual_092931

def g32p_supplierForest_node_084071 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨-1, -1⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_084071 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084071 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_095144 := by
  decide +kernel

theorem g32p_supplierForest_actual_084071 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084071) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_084071
    g32p_supplierForest_actual_095144

def g32p_supplierForest_node_084474 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_084474 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084474 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_089659 := by
  decide +kernel

theorem g32p_supplierForest_actual_084474 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084474) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084474
    g32p_supplierForest_actual_089659

def g32p_supplierForest_node_084731 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084731 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084731 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_020450 := by
  decide +kernel

theorem g32p_supplierForest_actual_084731 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084731) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 3 g32p_supplierForest_edge_084731
    g32p_supplierForest_actual_020450

def g32p_supplierForest_node_084798 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_084798 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084798 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090265 := by
  decide +kernel

theorem g32p_supplierForest_actual_084798 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084798) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_084798
    g32p_supplierForest_actual_090265

def g32p_supplierForest_node_084807 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨2, 0⟩, ⟨1, -1⟩, ⟨2, 1⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_084807 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084807 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_084617 := by
  decide +kernel

theorem g32p_supplierForest_actual_084807 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084807) ∧
        IsConj g (g32p_literalRepresentative 55) := by
  exact g32p_archive_step_lift _ _ 55 3 g32p_supplierForest_edge_084807
    g32p_supplierForest_actual_084617

def g32p_supplierForest_node_084955 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 2⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_084955 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_084955 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_019764 := by
  decide +kernel

theorem g32p_supplierForest_actual_084955 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_084955) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_084955
    g32p_supplierForest_actual_019764

def g32p_supplierForest_node_085462 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-2, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085462 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085462 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_087429 := by
  decide +kernel

theorem g32p_supplierForest_actual_085462 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085462) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_085462
    g32p_supplierForest_actual_087429

def g32p_supplierForest_node_085476 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085476 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085476 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_023839 := by
  decide +kernel

theorem g32p_supplierForest_actual_085476 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085476) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_085476
    g32p_supplierForest_actual_023839

def g32p_supplierForest_node_085592 : HurwitzPrymRex_Mat :=
  ![![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨-1, -2⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_085592 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085592 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_095627 := by
  decide +kernel

theorem g32p_supplierForest_actual_085592 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085592) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_085592
    g32p_supplierForest_actual_095627

def g32p_supplierForest_node_085801 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085801 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085801 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087514 := by
  decide +kernel

theorem g32p_supplierForest_actual_085801 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085801) ∧
        IsConj g (g32p_literalRepresentative 9) := by
  exact g32p_archive_step_lift _ _ 9 2 g32p_supplierForest_edge_085801
    g32p_supplierForest_actual_087514

def g32p_supplierForest_node_085815 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_085815 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_085815 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_080357 := by
  decide +kernel

theorem g32p_supplierForest_actual_085815 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_085815) ∧
        IsConj g (g32p_literalRepresentative 25) := by
  exact g32p_archive_step_lift _ _ 25 3 g32p_supplierForest_edge_085815
    g32p_supplierForest_actual_080357

def g32p_supplierForest_node_086441 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-2, -2⟩, ⟨-1, -2⟩, ⟨-1, -2⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_086441 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_086441 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084705 := by
  decide +kernel

theorem g32p_supplierForest_actual_086441 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_086441) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_086441
    g32p_supplierForest_actual_084705

def g32p_supplierForest_node_087004 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087004 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087004 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_082211 := by
  decide +kernel

theorem g32p_supplierForest_actual_087004 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087004) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_087004
    g32p_supplierForest_actual_082211

def g32p_supplierForest_node_087017 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087017 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087017 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_084682 := by
  decide +kernel

theorem g32p_supplierForest_actual_087017 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087017) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_087017
    g32p_supplierForest_actual_084682

def g32p_supplierForest_node_087168 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -2⟩, ⟨0, -2⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087168 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087168 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_146854 := by
  decide +kernel

theorem g32p_supplierForest_actual_087168 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087168) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_087168
    g32p_supplierForest_actual_146854

def g32p_supplierForest_node_087238 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, -2⟩, ⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, 1⟩], ![⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_087238 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087238 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_094461 := by
  decide +kernel

theorem g32p_supplierForest_actual_087238 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087238) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_087238
    g32p_supplierForest_actual_094461

def g32p_supplierForest_node_087632 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -2⟩, ⟨-1, -1⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087632 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087632 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_088520 := by
  decide +kernel

theorem g32p_supplierForest_actual_087632 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087632) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_087632
    g32p_supplierForest_actual_088520

def g32p_supplierForest_node_087908 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -2⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_087908 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_087908 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_097138 := by
  decide +kernel

theorem g32p_supplierForest_actual_087908 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_087908) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_087908
    g32p_supplierForest_actual_097138

def g32p_supplierForest_node_088174 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_088174 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088174 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_085417 := by
  decide +kernel

theorem g32p_supplierForest_actual_088174 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088174) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_088174
    g32p_supplierForest_actual_085417

def g32p_supplierForest_node_088268 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨-1, 1⟩, ⟨-1, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088268 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088268 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_096600 := by
  decide +kernel

theorem g32p_supplierForest_actual_088268 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088268) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_088268
    g32p_supplierForest_actual_096600

def g32p_supplierForest_node_088303 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088303 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088303 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_020936 := by
  decide +kernel

theorem g32p_supplierForest_actual_088303 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088303) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_088303
    g32p_supplierForest_actual_020936

def g32p_supplierForest_node_088852 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088852 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088852 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_074628 := by
  decide +kernel

theorem g32p_supplierForest_actual_088852 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088852) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_088852
    g32p_supplierForest_actual_074628

def g32p_supplierForest_node_088854 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨-1, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 2⟩]]

theorem g32p_supplierForest_edge_088854 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088854 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_101369 := by
  decide +kernel

theorem g32p_supplierForest_actual_088854 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088854) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_088854
    g32p_supplierForest_actual_101369

def g32p_supplierForest_node_088957 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_088957 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088957 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_081899 := by
  decide +kernel

theorem g32p_supplierForest_actual_088957 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088957) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 0 g32p_supplierForest_edge_088957
    g32p_supplierForest_actual_081899

def g32p_supplierForest_node_088973 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088973 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088973 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_015330 := by
  decide +kernel

theorem g32p_supplierForest_actual_088973 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088973) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 2 g32p_supplierForest_edge_088973
    g32p_supplierForest_actual_015330

def g32p_supplierForest_node_088980 : HurwitzPrymRex_Mat :=
  ![![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 0⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_088980 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088980 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_146137 := by
  decide +kernel

theorem g32p_supplierForest_actual_088980 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088980) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 1 g32p_supplierForest_edge_088980
    g32p_supplierForest_actual_146137

def g32p_supplierForest_node_088982 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_088982 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_088982 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_024473 := by
  decide +kernel

theorem g32p_supplierForest_actual_088982 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_088982) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_088982
    g32p_supplierForest_actual_024473

def g32p_supplierForest_node_089647 : HurwitzPrymRex_Mat :=
  ![![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-2, -2⟩, ⟨-2, -1⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_089647 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089647 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_099337 := by
  decide +kernel

theorem g32p_supplierForest_actual_089647 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089647) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 3 g32p_supplierForest_edge_089647
    g32p_supplierForest_actual_099337

def g32p_supplierForest_node_089989 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_089989 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_089989 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_098971 := by
  decide +kernel

theorem g32p_supplierForest_actual_089989 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_089989) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 1 g32p_supplierForest_edge_089989
    g32p_supplierForest_actual_098971

def g32p_supplierForest_node_090040 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, 0⟩], ![⟨2, 2⟩, ⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, 0⟩, ⟨-1, 0⟩, ⟨-1, -1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_090040 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090040 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_021438 := by
  decide +kernel

theorem g32p_supplierForest_actual_090040 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090040) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_090040
    g32p_supplierForest_actual_021438

def g32p_supplierForest_node_090047 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨-2, -2⟩, ⟨-1, 0⟩, ⟨0, -2⟩], ![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090047 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090047 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_084222 := by
  decide +kernel

theorem g32p_supplierForest_actual_090047 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090047) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_090047
    g32p_supplierForest_actual_084222

def g32p_supplierForest_node_090143 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨0, 2⟩, ⟨0, 0⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -2⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090143 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090143 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_091887 := by
  decide +kernel

theorem g32p_supplierForest_actual_090143 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090143) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_090143
    g32p_supplierForest_actual_091887

def g32p_supplierForest_node_090218 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-2, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090218 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090218 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_090926 := by
  decide +kernel

theorem g32p_supplierForest_actual_090218 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090218) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 2 g32p_supplierForest_edge_090218
    g32p_supplierForest_actual_090926

def g32p_supplierForest_node_090355 : HurwitzPrymRex_Mat :=
  ![![⟨-2, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨2, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨1, 0⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_090355 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090355 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_082750 := by
  decide +kernel

theorem g32p_supplierForest_actual_090355 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090355) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_090355
    g32p_supplierForest_actual_082750

def g32p_supplierForest_node_090400 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 2⟩, ⟨2, 2⟩, ⟨0, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨-1, -1⟩, ⟨-1, -1⟩]]

theorem g32p_supplierForest_edge_090400 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090400 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_150713 := by
  decide +kernel

theorem g32p_supplierForest_actual_090400 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090400) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_090400
    g32p_supplierForest_actual_150713

def g32p_supplierForest_node_090504 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨1, 1⟩], ![⟨0, 1⟩, ⟨-1, 1⟩, ⟨0, 1⟩, ⟨-2, -1⟩], ![⟨1, 0⟩, ⟨2, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨-1, -1⟩, ⟨0, -1⟩, ⟨0, -1⟩, ⟨1, 0⟩]]

theorem g32p_supplierForest_edge_090504 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090504 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_079171 := by
  decide +kernel

theorem g32p_supplierForest_actual_090504 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090504) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 0 g32p_supplierForest_edge_090504
    g32p_supplierForest_actual_079171

def g32p_supplierForest_node_090576 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 1⟩, ⟨-1, -2⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨1, 1⟩, ⟨1, 1⟩, ⟨0, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_090576 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090576 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_073349 := by
  decide +kernel

theorem g32p_supplierForest_actual_090576 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090576) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_090576
    g32p_supplierForest_actual_073349

def g32p_supplierForest_node_090653 : HurwitzPrymRex_Mat :=
  ![![⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, -1⟩]]

theorem g32p_supplierForest_edge_090653 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090653 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_090287 := by
  decide +kernel

theorem g32p_supplierForest_actual_090653 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090653) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_090653
    g32p_supplierForest_actual_090287

def g32p_supplierForest_node_090769 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩, ⟨1, -1⟩], ![⟨-1, -1⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_090769 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090769 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_087352 := by
  decide +kernel

theorem g32p_supplierForest_actual_090769 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090769) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_090769
    g32p_supplierForest_actual_087352

def g32p_supplierForest_node_090881 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 1⟩], ![⟨0, 0⟩, ⟨0, -2⟩, ⟨-1, -1⟩, ⟨1, -1⟩], ![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_090881 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_090881 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_100766 := by
  decide +kernel

theorem g32p_supplierForest_actual_090881 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_090881) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 0 g32p_supplierForest_edge_090881
    g32p_supplierForest_actual_100766

def g32p_supplierForest_node_091877 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 1⟩], ![⟨1, 0⟩, ⟨1, 0⟩, ⟨2, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 1⟩]]

theorem g32p_supplierForest_edge_091877 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_091877 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_022039 := by
  decide +kernel

theorem g32p_supplierForest_actual_091877 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_091877) ∧
        IsConj g (g32p_literalRepresentative 50) := by
  exact g32p_archive_step_lift _ _ 50 2 g32p_supplierForest_edge_091877
    g32p_supplierForest_actual_022039

def g32p_supplierForest_node_092285 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 0⟩], ![⟨-1, 0⟩, ⟨-2, -1⟩, ⟨0, 1⟩, ⟨-1, -1⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_092285 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092285 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_076537 := by
  decide +kernel

theorem g32p_supplierForest_actual_092285 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092285) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 3 g32p_supplierForest_edge_092285
    g32p_supplierForest_actual_076537

def g32p_supplierForest_node_092762 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨-1, 0⟩, ⟨0, 0⟩, ⟨-2, -1⟩], ![⟨-1, 0⟩, ⟨0, -1⟩, ⟨-1, 0⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 0⟩, ⟨0, -1⟩], ![⟨0, 0⟩, ⟨0, 1⟩, ⟨0, 0⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_092762 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092762 (g32p_archiveIntegralGenerators 3) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 3) g32p_supplierForest_node_083180 := by
  decide +kernel

theorem g32p_supplierForest_actual_092762 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092762) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 3 g32p_supplierForest_edge_092762
    g32p_supplierForest_actual_083180

def g32p_supplierForest_node_092912 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨0, -1⟩], ![⟨0, 1⟩, ⟨-1, 0⟩, ⟨-1, 1⟩, ⟨0, 1⟩], ![⟨0, 0⟩, ⟨1, 1⟩, ⟨1, 0⟩, ⟨1, 1⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_092912 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_092912 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_098454 := by
  decide +kernel

theorem g32p_supplierForest_actual_092912 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_092912) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_092912
    g32p_supplierForest_actual_098454

def g32p_supplierForest_node_093009 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨1, 1⟩], ![⟨1, 1⟩, ⟨-1, 0⟩, ⟨0, 1⟩, ⟨-2, -2⟩], ![⟨0, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨0, 1⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, -1⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093009 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093009 (g32p_archiveIntegralGenerators 1) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 1) g32p_supplierForest_node_077696 := by
  decide +kernel

theorem g32p_supplierForest_actual_093009 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093009) ∧
        IsConj g (g32p_literalRepresentative 49) := by
  exact g32p_archive_step_lift _ _ 49 1 g32p_supplierForest_edge_093009
    g32p_supplierForest_actual_077696

def g32p_supplierForest_node_093265 : HurwitzPrymRex_Mat :=
  ![![⟨1, 0⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩], ![⟨-2, -1⟩, ⟨-1, -2⟩, ⟨-2, -2⟩, ⟨1, 0⟩], ![⟨1, 2⟩, ⟨0, 1⟩, ⟨0, 1⟩, ⟨0, 0⟩], ![⟨1, 0⟩, ⟨1, 1⟩, ⟨2, 1⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093265 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093265 (g32p_archiveIntegralGenerators 0) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 0) g32p_supplierForest_node_090200 := by
  decide +kernel

theorem g32p_supplierForest_actual_093265 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093265) ∧
        IsConj g (g32p_literalRepresentative 26) := by
  exact g32p_archive_step_lift _ _ 26 0 g32p_supplierForest_edge_093265
    g32p_supplierForest_actual_090200

def g32p_supplierForest_node_093598 : HurwitzPrymRex_Mat :=
  ![![⟨0, -1⟩, ⟨0, -1⟩, ⟨0, 0⟩, ⟨1, 0⟩], ![⟨1, 1⟩, ⟨1, 2⟩, ⟨1, 0⟩, ⟨-1, 0⟩], ![⟨0, 0⟩, ⟨0, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩], ![⟨-1, -1⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩]]

theorem g32p_supplierForest_edge_093598 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093598 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_083437 := by
  decide +kernel

theorem g32p_supplierForest_actual_093598 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093598) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093598
    g32p_supplierForest_actual_083437

def g32p_supplierForest_node_093818 : HurwitzPrymRex_Mat :=
  ![![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨1, 1⟩], ![⟨2, 2⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, -1⟩], ![⟨0, -1⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩, ⟨1, 1⟩]]

theorem g32p_supplierForest_edge_093818 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093818 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_092397 := by
  decide +kernel

theorem g32p_supplierForest_actual_093818 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093818) ∧
        IsConj g (g32p_literalRepresentative 47) := by
  exact g32p_archive_step_lift _ _ 47 2 g32p_supplierForest_edge_093818
    g32p_supplierForest_actual_092397

def g32p_supplierForest_node_093986 : HurwitzPrymRex_Mat :=
  ![![⟨0, 0⟩, ⟨0, 0⟩, ⟨0, 0⟩, ⟨-1, 0⟩], ![⟨-1, -1⟩, ⟨1, 0⟩, ⟨0, -1⟩, ⟨2, 1⟩], ![⟨0, 0⟩, ⟨-1, -1⟩, ⟨0, 0⟩, ⟨-1, -2⟩], ![⟨1, 1⟩, ⟨0, 1⟩, ⟨1, 1⟩, ⟨-1, 0⟩]]

theorem g32p_supplierForest_edge_093986 :
    HurwitzPrymRex_mmul g32p_supplierForest_node_093986 (g32p_archiveIntegralGenerators 2) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators 2) g32p_supplierForest_node_096587 := by
  decide +kernel

theorem g32p_supplierForest_actual_093986 :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega g32p_supplierForest_node_093986) ∧
        IsConj g (g32p_literalRepresentative 46) := by
  exact g32p_archive_step_lift _ _ 46 2 g32p_supplierForest_edge_093986
    g32p_supplierForest_actual_096587

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

def g32p_supplierForest_nodes_136 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_064466 else g32p_supplierForest_node_064471) else (if i.val < 3 then g32p_supplierForest_node_064494 else g32p_supplierForest_node_064521)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_064540 else g32p_supplierForest_node_064543) else (if i.val < 7 then g32p_supplierForest_node_064549 else g32p_supplierForest_node_064560))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_064580 else g32p_supplierForest_node_064665) else (if i.val < 11 then g32p_supplierForest_node_064683 else g32p_supplierForest_node_064713)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_064731 else g32p_supplierForest_node_064737) else (if i.val < 15 then g32p_supplierForest_node_064773 else g32p_supplierForest_node_064849)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_064888 else g32p_supplierForest_node_064889) else (if i.val < 19 then g32p_supplierForest_node_064921 else g32p_supplierForest_node_064981)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_064997 else g32p_supplierForest_node_065156) else (if i.val < 23 then g32p_supplierForest_node_065168 else g32p_supplierForest_node_065170))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_065411 else g32p_supplierForest_node_065445) else (if i.val < 27 then g32p_supplierForest_node_065455 else g32p_supplierForest_node_065489)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_065512 else g32p_supplierForest_node_065547) else (if i.val < 31 then g32p_supplierForest_node_065630 else g32p_supplierForest_node_065805))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_065834 else g32p_supplierForest_node_065907) else (if i.val < 35 then g32p_supplierForest_node_065991 else g32p_supplierForest_node_066090)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_066100 else g32p_supplierForest_node_066104) else (if i.val < 39 then g32p_supplierForest_node_066152 else g32p_supplierForest_node_066188))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_066237 else g32p_supplierForest_node_066251) else (if i.val < 43 then g32p_supplierForest_node_066268 else g32p_supplierForest_node_066281)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_066345 else g32p_supplierForest_node_066361) else (if i.val < 47 then g32p_supplierForest_node_066382 else g32p_supplierForest_node_066710)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_066778 else g32p_supplierForest_node_066790) else (if i.val < 51 then g32p_supplierForest_node_066875 else g32p_supplierForest_node_066884)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_066907 else g32p_supplierForest_node_066965) else (if i.val < 55 then g32p_supplierForest_node_067107 else g32p_supplierForest_node_067166))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_067179 else g32p_supplierForest_node_067277) else (if i.val < 59 then g32p_supplierForest_node_067319 else g32p_supplierForest_node_067334)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_067341 else g32p_supplierForest_node_067342) else (if i.val < 63 then g32p_supplierForest_node_067376 else g32p_supplierForest_node_067420)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_067447 else g32p_supplierForest_node_067478) else (if i.val < 67 then g32p_supplierForest_node_067518 else g32p_supplierForest_node_067531)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_067672 else g32p_supplierForest_node_067809) else (if i.val < 71 then g32p_supplierForest_node_068024 else g32p_supplierForest_node_068037))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_068117 else g32p_supplierForest_node_068482) else (if i.val < 75 then g32p_supplierForest_node_068513 else g32p_supplierForest_node_068707)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_068722 else g32p_supplierForest_node_068738) else (if i.val < 79 then g32p_supplierForest_node_068788 else g32p_supplierForest_node_068792)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_068835 else g32p_supplierForest_node_068884) else (if i.val < 83 then g32p_supplierForest_node_068898 else g32p_supplierForest_node_068903)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_068998 else g32p_supplierForest_node_069030) else (if i.val < 87 then g32p_supplierForest_node_069095 else g32p_supplierForest_node_069113))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_069136 else g32p_supplierForest_node_069158) else (if i.val < 91 then g32p_supplierForest_node_069183 else g32p_supplierForest_node_069221)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_069273 else g32p_supplierForest_node_069294) else (if i.val < 95 then g32p_supplierForest_node_069308 else g32p_supplierForest_node_069382))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_069397 else g32p_supplierForest_node_069414) else (if i.val < 99 then g32p_supplierForest_node_069625 else g32p_supplierForest_node_069741)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_069749 else g32p_supplierForest_node_069768) else (if i.val < 103 then g32p_supplierForest_node_069878 else g32p_supplierForest_node_069888))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_070009 else g32p_supplierForest_node_070046) else (if i.val < 107 then g32p_supplierForest_node_070091 else g32p_supplierForest_node_070123)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_070129 else g32p_supplierForest_node_070200) else (if i.val < 111 then g32p_supplierForest_node_070211 else g32p_supplierForest_node_070323)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_070353 else g32p_supplierForest_node_070380) else (if i.val < 115 then g32p_supplierForest_node_070436 else g32p_supplierForest_node_070485)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_070630 else g32p_supplierForest_node_070638) else (if i.val < 119 then g32p_supplierForest_node_070853 else g32p_supplierForest_node_070860))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_070971 else g32p_supplierForest_node_070985) else (if i.val < 123 then g32p_supplierForest_node_071002 else g32p_supplierForest_node_071008)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_071081 else g32p_supplierForest_node_071087) else (if i.val < 127 then g32p_supplierForest_node_071119 else g32p_supplierForest_node_071142))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_071184 else g32p_supplierForest_node_071186) else (if i.val < 131 then g32p_supplierForest_node_071256 else g32p_supplierForest_node_071294)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_071353 else g32p_supplierForest_node_071366) else (if i.val < 135 then g32p_supplierForest_node_071405 else g32p_supplierForest_node_071540))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_071621 else g32p_supplierForest_node_071788) else (if i.val < 139 then g32p_supplierForest_node_071871 else g32p_supplierForest_node_071891)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_071916 else g32p_supplierForest_node_071961) else (if i.val < 143 then g32p_supplierForest_node_072077 else g32p_supplierForest_node_072099)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_072114 else g32p_supplierForest_node_072182) else (if i.val < 147 then g32p_supplierForest_node_072215 else g32p_supplierForest_node_072301)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_072316 else g32p_supplierForest_node_072338) else (if i.val < 151 then g32p_supplierForest_node_072360 else g32p_supplierForest_node_072370))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_072408 else g32p_supplierForest_node_072469) else (if i.val < 155 then g32p_supplierForest_node_072481 else g32p_supplierForest_node_072504)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_072509 else g32p_supplierForest_node_072633) else (if i.val < 159 then g32p_supplierForest_node_072732 else g32p_supplierForest_node_072817))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_072841 else g32p_supplierForest_node_072893) else (if i.val < 163 then g32p_supplierForest_node_072950 else g32p_supplierForest_node_072964)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_073118 else g32p_supplierForest_node_073147) else (if i.val < 167 then g32p_supplierForest_node_073171 else g32p_supplierForest_node_073234))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_073332 else g32p_supplierForest_node_073349) else (if i.val < 171 then g32p_supplierForest_node_073512 else g32p_supplierForest_node_073571)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_073584 else g32p_supplierForest_node_073734) else (if i.val < 175 then g32p_supplierForest_node_073813 else g32p_supplierForest_node_073824)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_073932 else g32p_supplierForest_node_073990) else (if i.val < 179 then g32p_supplierForest_node_074328 else g32p_supplierForest_node_074357)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_074368 else g32p_supplierForest_node_074422) else (if i.val < 183 then g32p_supplierForest_node_074454 else g32p_supplierForest_node_074514))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_074561 else g32p_supplierForest_node_074591) else (if i.val < 187 then g32p_supplierForest_node_074628 else g32p_supplierForest_node_074722)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_074767 else g32p_supplierForest_node_074841) else (if i.val < 191 then g32p_supplierForest_node_074874 else g32p_supplierForest_node_074877)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_074883 else g32p_supplierForest_node_074948) else (if i.val < 195 then g32p_supplierForest_node_074970 else g32p_supplierForest_node_074982)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_075057 else g32p_supplierForest_node_075075) else (if i.val < 199 then g32p_supplierForest_node_075084 else g32p_supplierForest_node_075178))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_075197 else g32p_supplierForest_node_075229) else (if i.val < 203 then g32p_supplierForest_node_075279 else g32p_supplierForest_node_075411)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_075416 else g32p_supplierForest_node_075471) else (if i.val < 207 then g32p_supplierForest_node_075508 else g32p_supplierForest_node_075539)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_075701 else g32p_supplierForest_node_075710) else (if i.val < 211 then g32p_supplierForest_node_075745 else g32p_supplierForest_node_075758)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_075844 else g32p_supplierForest_node_076023) else (if i.val < 215 then g32p_supplierForest_node_076034 else g32p_supplierForest_node_076039))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_076040 else g32p_supplierForest_node_076044) else (if i.val < 219 then g32p_supplierForest_node_076051 else g32p_supplierForest_node_076052)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_076164 else g32p_supplierForest_node_076233) else (if i.val < 223 then g32p_supplierForest_node_076275 else g32p_supplierForest_node_076284))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_076357 else g32p_supplierForest_node_076412) else (if i.val < 227 then g32p_supplierForest_node_076414 else g32p_supplierForest_node_076435)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_076514 else g32p_supplierForest_node_076529) else (if i.val < 231 then g32p_supplierForest_node_076537 else g32p_supplierForest_node_076617))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_076696 else g32p_supplierForest_node_076756) else (if i.val < 235 then g32p_supplierForest_node_076825 else g32p_supplierForest_node_076833)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_076966 else g32p_supplierForest_node_077189) else (if i.val < 239 then g32p_supplierForest_node_077258 else g32p_supplierForest_node_077366)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_077435 else g32p_supplierForest_node_077436) else (if i.val < 243 then g32p_supplierForest_node_077510 else g32p_supplierForest_node_077515)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_077557 else g32p_supplierForest_node_077634) else (if i.val < 247 then g32p_supplierForest_node_077662 else g32p_supplierForest_node_077668))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_077676 else g32p_supplierForest_node_077696) else (if i.val < 251 then g32p_supplierForest_node_077767 else g32p_supplierForest_node_077850)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_077876 else g32p_supplierForest_node_077900) else (if i.val < 255 then g32p_supplierForest_node_077951 else g32p_supplierForest_node_077983))))))))

def g32p_supplierForest_classes_136 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 20 else 22) else (if i.val < 3 then 74 else 38)) else (if i.val < 6 then (if i.val < 5 then 68 else 71) else (if i.val < 7 then 38 else 70))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 21) else (if i.val < 11 then 21 else 38)) else (if i.val < 14 then (if i.val < 13 then 73 else 70) else (if i.val < 15 then 21 else 71)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 38) else (if i.val < 19 then 21 else 21)) else (if i.val < 22 then (if i.val < 21 then 21 else 21) else (if i.val < 23 then 41 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 38) else (if i.val < 27 then 38 else 40)) else (if i.val < 30 then (if i.val < 29 then 40 else 21) else (if i.val < 31 then 38 else 38))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 41 else 38) else (if i.val < 35 then 73 else 38)) else (if i.val < 38 then (if i.val < 37 then 38 else 21) else (if i.val < 39 then 38 else 73))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 40 else 22) else (if i.val < 43 then 38 else 70)) else (if i.val < 46 then (if i.val < 45 then 42 else 40) else (if i.val < 47 then 21 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 74 else 75) else (if i.val < 51 then 21 else 68)) else (if i.val < 54 then (if i.val < 53 then 21 else 38) else (if i.val < 55 then 20 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 21) else (if i.val < 59 then 38 else 38)) else (if i.val < 62 then (if i.val < 61 then 21 else 21) else (if i.val < 63 then 73 else 22)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 38 else 42) else (if i.val < 67 then 21 else 72)) else (if i.val < 70 then (if i.val < 69 then 7 else 22) else (if i.val < 71 then 21 else 38))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 21 else 73) else (if i.val < 75 then 38 else 21)) else (if i.val < 78 then (if i.val < 77 then 20 else 21) else (if i.val < 79 then 20 else 73)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 38 else 38) else (if i.val < 83 then 38 else 21)) else (if i.val < 86 then (if i.val < 85 then 42 else 21) else (if i.val < 87 then 38 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 38 else 21) else (if i.val < 91 then 22 else 22)) else (if i.val < 94 then (if i.val < 93 then 38 else 38) else (if i.val < 95 then 38 else 38))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 38 else 21) else (if i.val < 99 then 21 else 38)) else (if i.val < 102 then (if i.val < 101 then 73 else 41) else (if i.val < 103 then 38 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 38) else (if i.val < 107 then 38 else 38)) else (if i.val < 110 then (if i.val < 109 then 38 else 38) else (if i.val < 111 then 38 else 73)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 38 else 70) else (if i.val < 115 then 21 else 38)) else (if i.val < 118 then (if i.val < 117 then 21 else 21) else (if i.val < 119 then 40 else 21))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 40 else 38) else (if i.val < 123 then 21 else 38)) else (if i.val < 126 then (if i.val < 125 then 7 else 21) else (if i.val < 127 then 38 else 22))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 73 else 72) else (if i.val < 131 then 42 else 21)) else (if i.val < 134 then (if i.val < 133 then 38 else 38) else (if i.val < 135 then 38 else 73))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 21 else 46) else (if i.val < 139 then 48 else 49)) else (if i.val < 142 then (if i.val < 141 then 49 else 49) else (if i.val < 143 then 49 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 49 else 49) else (if i.val < 147 then 49 else 49)) else (if i.val < 150 then (if i.val < 149 then 47 else 49) else (if i.val < 151 then 80 else 26))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 47 else 49) else (if i.val < 155 then 49 else 26)) else (if i.val < 158 then (if i.val < 157 then 26 else 49) else (if i.val < 159 then 49 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 49 else 25) else (if i.val < 163 then 27 else 49)) else (if i.val < 166 then (if i.val < 165 then 49 else 49) else (if i.val < 167 then 49 else 47))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 49 else 49) else (if i.val < 171 then 49 else 49)) else (if i.val < 174 then (if i.val < 173 then 12 else 49) else (if i.val < 175 then 49 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 49 else 49) else (if i.val < 179 then 50 else 26)) else (if i.val < 182 then (if i.val < 181 then 49 else 55) else (if i.val < 183 then 49 else 47))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 46) else (if i.val < 187 then 46 else 26)) else (if i.val < 190 then (if i.val < 189 then 53 else 49) else (if i.val < 191 then 49 else 46)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 46 else 46) else (if i.val < 195 then 49 else 10)) else (if i.val < 198 then (if i.val < 197 then 46 else 25) else (if i.val < 199 then 49 else 26))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 46 else 46) else (if i.val < 203 then 27 else 49)) else (if i.val < 206 then (if i.val < 205 then 26 else 55) else (if i.val < 207 then 49 else 46)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 46) else (if i.val < 211 then 46 else 50)) else (if i.val < 214 then (if i.val < 213 then 46 else 49) else (if i.val < 215 then 49 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 47 else 46) else (if i.val < 219 then 25 else 46)) else (if i.val < 222 then (if i.val < 221 then 49 else 49) else (if i.val < 223 then 49 else 12))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 49 else 46) else (if i.val < 227 then 27 else 53)) else (if i.val < 230 then (if i.val < 229 then 47 else 50) else (if i.val < 231 then 49 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 9) else (if i.val < 235 then 49 else 12)) else (if i.val < 238 then (if i.val < 237 then 47 else 27) else (if i.val < 239 then 47 else 49)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 46) else (if i.val < 243 then 49 else 46)) else (if i.val < 246 then (if i.val < 245 then 49 else 46) else (if i.val < 247 then 49 else 49))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 49) else (if i.val < 251 then 49 else 26)) else (if i.val < 254 then (if i.val < 253 then 46 else 46) else (if i.val < 255 then 26 else 46))))))))

theorem g32p_supplierForest_actual_136 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_136 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_136 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_064466
  · exact g32p_supplierForest_actual_064471
  · exact g32p_supplierForest_actual_064494
  · exact g32p_supplierForest_actual_064521
  · exact g32p_supplierForest_actual_064540
  · exact g32p_supplierForest_actual_064543
  · exact g32p_supplierForest_actual_064549
  · exact g32p_supplierForest_actual_064560
  · exact g32p_supplierForest_actual_064580
  · exact g32p_supplierForest_actual_064665
  · exact g32p_supplierForest_actual_064683
  · exact g32p_supplierForest_actual_064713
  · exact g32p_supplierForest_actual_064731
  · exact g32p_supplierForest_actual_064737
  · exact g32p_supplierForest_actual_064773
  · exact g32p_supplierForest_actual_064849
  · exact g32p_supplierForest_actual_064888
  · exact g32p_supplierForest_actual_064889
  · exact g32p_supplierForest_actual_064921
  · exact g32p_supplierForest_actual_064981
  · exact g32p_supplierForest_actual_064997
  · exact g32p_supplierForest_actual_065156
  · exact g32p_supplierForest_actual_065168
  · exact g32p_supplierForest_actual_065170
  · exact g32p_supplierForest_actual_065411
  · exact g32p_supplierForest_actual_065445
  · exact g32p_supplierForest_actual_065455
  · exact g32p_supplierForest_actual_065489
  · exact g32p_supplierForest_actual_065512
  · exact g32p_supplierForest_actual_065547
  · exact g32p_supplierForest_actual_065630
  · exact g32p_supplierForest_actual_065805
  · exact g32p_supplierForest_actual_065834
  · exact g32p_supplierForest_actual_065907
  · exact g32p_supplierForest_actual_065991
  · exact g32p_supplierForest_actual_066090
  · exact g32p_supplierForest_actual_066100
  · exact g32p_supplierForest_actual_066104
  · exact g32p_supplierForest_actual_066152
  · exact g32p_supplierForest_actual_066188
  · exact g32p_supplierForest_actual_066237
  · exact g32p_supplierForest_actual_066251
  · exact g32p_supplierForest_actual_066268
  · exact g32p_supplierForest_actual_066281
  · exact g32p_supplierForest_actual_066345
  · exact g32p_supplierForest_actual_066361
  · exact g32p_supplierForest_actual_066382
  · exact g32p_supplierForest_actual_066710
  · exact g32p_supplierForest_actual_066778
  · exact g32p_supplierForest_actual_066790
  · exact g32p_supplierForest_actual_066875
  · exact g32p_supplierForest_actual_066884
  · exact g32p_supplierForest_actual_066907
  · exact g32p_supplierForest_actual_066965
  · exact g32p_supplierForest_actual_067107
  · exact g32p_supplierForest_actual_067166
  · exact g32p_supplierForest_actual_067179
  · exact g32p_supplierForest_actual_067277
  · exact g32p_supplierForest_actual_067319
  · exact g32p_supplierForest_actual_067334
  · exact g32p_supplierForest_actual_067341
  · exact g32p_supplierForest_actual_067342
  · exact g32p_supplierForest_actual_067376
  · exact g32p_supplierForest_actual_067420
  · exact g32p_supplierForest_actual_067447
  · exact g32p_supplierForest_actual_067478
  · exact g32p_supplierForest_actual_067518
  · exact g32p_supplierForest_actual_067531
  · exact g32p_supplierForest_actual_067672
  · exact g32p_supplierForest_actual_067809
  · exact g32p_supplierForest_actual_068024
  · exact g32p_supplierForest_actual_068037
  · exact g32p_supplierForest_actual_068117
  · exact g32p_supplierForest_actual_068482
  · exact g32p_supplierForest_actual_068513
  · exact g32p_supplierForest_actual_068707
  · exact g32p_supplierForest_actual_068722
  · exact g32p_supplierForest_actual_068738
  · exact g32p_supplierForest_actual_068788
  · exact g32p_supplierForest_actual_068792
  · exact g32p_supplierForest_actual_068835
  · exact g32p_supplierForest_actual_068884
  · exact g32p_supplierForest_actual_068898
  · exact g32p_supplierForest_actual_068903
  · exact g32p_supplierForest_actual_068998
  · exact g32p_supplierForest_actual_069030
  · exact g32p_supplierForest_actual_069095
  · exact g32p_supplierForest_actual_069113
  · exact g32p_supplierForest_actual_069136
  · exact g32p_supplierForest_actual_069158
  · exact g32p_supplierForest_actual_069183
  · exact g32p_supplierForest_actual_069221
  · exact g32p_supplierForest_actual_069273
  · exact g32p_supplierForest_actual_069294
  · exact g32p_supplierForest_actual_069308
  · exact g32p_supplierForest_actual_069382
  · exact g32p_supplierForest_actual_069397
  · exact g32p_supplierForest_actual_069414
  · exact g32p_supplierForest_actual_069625
  · exact g32p_supplierForest_actual_069741
  · exact g32p_supplierForest_actual_069749
  · exact g32p_supplierForest_actual_069768
  · exact g32p_supplierForest_actual_069878
  · exact g32p_supplierForest_actual_069888
  · exact g32p_supplierForest_actual_070009
  · exact g32p_supplierForest_actual_070046
  · exact g32p_supplierForest_actual_070091
  · exact g32p_supplierForest_actual_070123
  · exact g32p_supplierForest_actual_070129
  · exact g32p_supplierForest_actual_070200
  · exact g32p_supplierForest_actual_070211
  · exact g32p_supplierForest_actual_070323
  · exact g32p_supplierForest_actual_070353
  · exact g32p_supplierForest_actual_070380
  · exact g32p_supplierForest_actual_070436
  · exact g32p_supplierForest_actual_070485
  · exact g32p_supplierForest_actual_070630
  · exact g32p_supplierForest_actual_070638
  · exact g32p_supplierForest_actual_070853
  · exact g32p_supplierForest_actual_070860
  · exact g32p_supplierForest_actual_070971
  · exact g32p_supplierForest_actual_070985
  · exact g32p_supplierForest_actual_071002
  · exact g32p_supplierForest_actual_071008
  · exact g32p_supplierForest_actual_071081
  · exact g32p_supplierForest_actual_071087
  · exact g32p_supplierForest_actual_071119
  · exact g32p_supplierForest_actual_071142
  · exact g32p_supplierForest_actual_071184
  · exact g32p_supplierForest_actual_071186
  · exact g32p_supplierForest_actual_071256
  · exact g32p_supplierForest_actual_071294
  · exact g32p_supplierForest_actual_071353
  · exact g32p_supplierForest_actual_071366
  · exact g32p_supplierForest_actual_071405
  · exact g32p_supplierForest_actual_071540
  · exact g32p_supplierForest_actual_071621
  · exact g32p_supplierForest_actual_071788
  · exact g32p_supplierForest_actual_071871
  · exact g32p_supplierForest_actual_071891
  · exact g32p_supplierForest_actual_071916
  · exact g32p_supplierForest_actual_071961
  · exact g32p_supplierForest_actual_072077
  · exact g32p_supplierForest_actual_072099
  · exact g32p_supplierForest_actual_072114
  · exact g32p_supplierForest_actual_072182
  · exact g32p_supplierForest_actual_072215
  · exact g32p_supplierForest_actual_072301
  · exact g32p_supplierForest_actual_072316
  · exact g32p_supplierForest_actual_072338
  · exact g32p_supplierForest_actual_072360
  · exact g32p_supplierForest_actual_072370
  · exact g32p_supplierForest_actual_072408
  · exact g32p_supplierForest_actual_072469
  · exact g32p_supplierForest_actual_072481
  · exact g32p_supplierForest_actual_072504
  · exact g32p_supplierForest_actual_072509
  · exact g32p_supplierForest_actual_072633
  · exact g32p_supplierForest_actual_072732
  · exact g32p_supplierForest_actual_072817
  · exact g32p_supplierForest_actual_072841
  · exact g32p_supplierForest_actual_072893
  · exact g32p_supplierForest_actual_072950
  · exact g32p_supplierForest_actual_072964
  · exact g32p_supplierForest_actual_073118
  · exact g32p_supplierForest_actual_073147
  · exact g32p_supplierForest_actual_073171
  · exact g32p_supplierForest_actual_073234
  · exact g32p_supplierForest_actual_073332
  · exact g32p_supplierForest_actual_073349
  · exact g32p_supplierForest_actual_073512
  · exact g32p_supplierForest_actual_073571
  · exact g32p_supplierForest_actual_073584
  · exact g32p_supplierForest_actual_073734
  · exact g32p_supplierForest_actual_073813
  · exact g32p_supplierForest_actual_073824
  · exact g32p_supplierForest_actual_073932
  · exact g32p_supplierForest_actual_073990
  · exact g32p_supplierForest_actual_074328
  · exact g32p_supplierForest_actual_074357
  · exact g32p_supplierForest_actual_074368
  · exact g32p_supplierForest_actual_074422
  · exact g32p_supplierForest_actual_074454
  · exact g32p_supplierForest_actual_074514
  · exact g32p_supplierForest_actual_074561
  · exact g32p_supplierForest_actual_074591
  · exact g32p_supplierForest_actual_074628
  · exact g32p_supplierForest_actual_074722
  · exact g32p_supplierForest_actual_074767
  · exact g32p_supplierForest_actual_074841
  · exact g32p_supplierForest_actual_074874
  · exact g32p_supplierForest_actual_074877
  · exact g32p_supplierForest_actual_074883
  · exact g32p_supplierForest_actual_074948
  · exact g32p_supplierForest_actual_074970
  · exact g32p_supplierForest_actual_074982
  · exact g32p_supplierForest_actual_075057
  · exact g32p_supplierForest_actual_075075
  · exact g32p_supplierForest_actual_075084
  · exact g32p_supplierForest_actual_075178
  · exact g32p_supplierForest_actual_075197
  · exact g32p_supplierForest_actual_075229
  · exact g32p_supplierForest_actual_075279
  · exact g32p_supplierForest_actual_075411
  · exact g32p_supplierForest_actual_075416
  · exact g32p_supplierForest_actual_075471
  · exact g32p_supplierForest_actual_075508
  · exact g32p_supplierForest_actual_075539
  · exact g32p_supplierForest_actual_075701
  · exact g32p_supplierForest_actual_075710
  · exact g32p_supplierForest_actual_075745
  · exact g32p_supplierForest_actual_075758
  · exact g32p_supplierForest_actual_075844
  · exact g32p_supplierForest_actual_076023
  · exact g32p_supplierForest_actual_076034
  · exact g32p_supplierForest_actual_076039
  · exact g32p_supplierForest_actual_076040
  · exact g32p_supplierForest_actual_076044
  · exact g32p_supplierForest_actual_076051
  · exact g32p_supplierForest_actual_076052
  · exact g32p_supplierForest_actual_076164
  · exact g32p_supplierForest_actual_076233
  · exact g32p_supplierForest_actual_076275
  · exact g32p_supplierForest_actual_076284
  · exact g32p_supplierForest_actual_076357
  · exact g32p_supplierForest_actual_076412
  · exact g32p_supplierForest_actual_076414
  · exact g32p_supplierForest_actual_076435
  · exact g32p_supplierForest_actual_076514
  · exact g32p_supplierForest_actual_076529
  · exact g32p_supplierForest_actual_076537
  · exact g32p_supplierForest_actual_076617
  · exact g32p_supplierForest_actual_076696
  · exact g32p_supplierForest_actual_076756
  · exact g32p_supplierForest_actual_076825
  · exact g32p_supplierForest_actual_076833
  · exact g32p_supplierForest_actual_076966
  · exact g32p_supplierForest_actual_077189
  · exact g32p_supplierForest_actual_077258
  · exact g32p_supplierForest_actual_077366
  · exact g32p_supplierForest_actual_077435
  · exact g32p_supplierForest_actual_077436
  · exact g32p_supplierForest_actual_077510
  · exact g32p_supplierForest_actual_077515
  · exact g32p_supplierForest_actual_077557
  · exact g32p_supplierForest_actual_077634
  · exact g32p_supplierForest_actual_077662
  · exact g32p_supplierForest_actual_077668
  · exact g32p_supplierForest_actual_077676
  · exact g32p_supplierForest_actual_077696
  · exact g32p_supplierForest_actual_077767
  · exact g32p_supplierForest_actual_077850
  · exact g32p_supplierForest_actual_077876
  · exact g32p_supplierForest_actual_077900
  · exact g32p_supplierForest_actual_077951
  · exact g32p_supplierForest_actual_077983

def g32p_supplierForest_nodes_137 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_078037 else g32p_supplierForest_node_078045) else (if i.val < 3 then g32p_supplierForest_node_078115 else g32p_supplierForest_node_078153)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_078164 else g32p_supplierForest_node_078169) else (if i.val < 7 then g32p_supplierForest_node_078223 else g32p_supplierForest_node_078581))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_078620 else g32p_supplierForest_node_078689) else (if i.val < 11 then g32p_supplierForest_node_078784 else g32p_supplierForest_node_078797)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_078899 else g32p_supplierForest_node_078958) else (if i.val < 15 then g32p_supplierForest_node_078963 else g32p_supplierForest_node_078982)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_079023 else g32p_supplierForest_node_079041) else (if i.val < 19 then g32p_supplierForest_node_079046 else g32p_supplierForest_node_079135)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_079171 else g32p_supplierForest_node_079172) else (if i.val < 23 then g32p_supplierForest_node_079262 else g32p_supplierForest_node_079306))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_079316 else g32p_supplierForest_node_079378) else (if i.val < 27 then g32p_supplierForest_node_079449 else g32p_supplierForest_node_079492)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_079497 else g32p_supplierForest_node_079500) else (if i.val < 31 then g32p_supplierForest_node_079543 else g32p_supplierForest_node_079557))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_079568 else g32p_supplierForest_node_079603) else (if i.val < 35 then g32p_supplierForest_node_079701 else g32p_supplierForest_node_079798)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_079810 else g32p_supplierForest_node_079814) else (if i.val < 39 then g32p_supplierForest_node_079835 else g32p_supplierForest_node_079838))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_079845 else g32p_supplierForest_node_079893) else (if i.val < 43 then g32p_supplierForest_node_079948 else g32p_supplierForest_node_080040)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_080064 else g32p_supplierForest_node_080068) else (if i.val < 47 then g32p_supplierForest_node_080115 else g32p_supplierForest_node_080159)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_080227 else g32p_supplierForest_node_080265) else (if i.val < 51 then g32p_supplierForest_node_080332 else g32p_supplierForest_node_080353)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_080356 else g32p_supplierForest_node_080357) else (if i.val < 55 then g32p_supplierForest_node_080359 else g32p_supplierForest_node_080399))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_080418 else g32p_supplierForest_node_080432) else (if i.val < 59 then g32p_supplierForest_node_080483 else g32p_supplierForest_node_080553)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_080576 else g32p_supplierForest_node_080616) else (if i.val < 63 then g32p_supplierForest_node_080683 else g32p_supplierForest_node_080692)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_080706 else g32p_supplierForest_node_080742) else (if i.val < 67 then g32p_supplierForest_node_080774 else g32p_supplierForest_node_080799)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_080835 else g32p_supplierForest_node_080858) else (if i.val < 71 then g32p_supplierForest_node_080981 else g32p_supplierForest_node_081121))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_081228 else g32p_supplierForest_node_081254) else (if i.val < 75 then g32p_supplierForest_node_081270 else g32p_supplierForest_node_081272)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_081285 else g32p_supplierForest_node_081348) else (if i.val < 79 then g32p_supplierForest_node_081383 else g32p_supplierForest_node_081459)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_081460 else g32p_supplierForest_node_081463) else (if i.val < 83 then g32p_supplierForest_node_081555 else g32p_supplierForest_node_081588)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_081740 else g32p_supplierForest_node_081899) else (if i.val < 87 then g32p_supplierForest_node_081905 else g32p_supplierForest_node_081915))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_082102 else g32p_supplierForest_node_082188) else (if i.val < 91 then g32p_supplierForest_node_082211 else g32p_supplierForest_node_082224)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_082324 else g32p_supplierForest_node_082382) else (if i.val < 95 then g32p_supplierForest_node_082391 else g32p_supplierForest_node_082443))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_082464 else g32p_supplierForest_node_082476) else (if i.val < 99 then g32p_supplierForest_node_082530 else g32p_supplierForest_node_082577)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_082611 else g32p_supplierForest_node_082722) else (if i.val < 103 then g32p_supplierForest_node_082750 else g32p_supplierForest_node_083042))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_083180 else g32p_supplierForest_node_083230) else (if i.val < 107 then g32p_supplierForest_node_083251 else g32p_supplierForest_node_083330)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_083350 else g32p_supplierForest_node_083437) else (if i.val < 111 then g32p_supplierForest_node_083440 else g32p_supplierForest_node_083528)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_083565 else g32p_supplierForest_node_083602) else (if i.val < 115 then g32p_supplierForest_node_083712 else g32p_supplierForest_node_083739)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_083878 else g32p_supplierForest_node_083898) else (if i.val < 119 then g32p_supplierForest_node_084070 else g32p_supplierForest_node_084222))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_084246 else g32p_supplierForest_node_084255) else (if i.val < 123 then g32p_supplierForest_node_084310 else g32p_supplierForest_node_084359)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_084368 else g32p_supplierForest_node_084508) else (if i.val < 127 then g32p_supplierForest_node_084517 else g32p_supplierForest_node_084539))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_084552 else g32p_supplierForest_node_084605) else (if i.val < 131 then g32p_supplierForest_node_084617 else g32p_supplierForest_node_084682)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_084705 else g32p_supplierForest_node_084752) else (if i.val < 135 then g32p_supplierForest_node_084775 else g32p_supplierForest_node_084789))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_084830 else g32p_supplierForest_node_084974) else (if i.val < 139 then g32p_supplierForest_node_085024 else g32p_supplierForest_node_085073)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_085135 else g32p_supplierForest_node_085304) else (if i.val < 143 then g32p_supplierForest_node_085417 else g32p_supplierForest_node_085463)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_085593 else g32p_supplierForest_node_085856) else (if i.val < 147 then g32p_supplierForest_node_085865 else g32p_supplierForest_node_085912)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_085927 else g32p_supplierForest_node_086005) else (if i.val < 151 then g32p_supplierForest_node_086069 else g32p_supplierForest_node_086074))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_086161 else g32p_supplierForest_node_086183) else (if i.val < 155 then g32p_supplierForest_node_086374 else g32p_supplierForest_node_086428)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_086432 else g32p_supplierForest_node_086519) else (if i.val < 159 then g32p_supplierForest_node_086570 else g32p_supplierForest_node_086612))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_086637 else g32p_supplierForest_node_086692) else (if i.val < 163 then g32p_supplierForest_node_086769 else g32p_supplierForest_node_086807)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_086847 else g32p_supplierForest_node_086883) else (if i.val < 167 then g32p_supplierForest_node_087072 else g32p_supplierForest_node_087115))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_087118 else g32p_supplierForest_node_087134) else (if i.val < 171 then g32p_supplierForest_node_087153 else g32p_supplierForest_node_087211)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_087221 else g32p_supplierForest_node_087241) else (if i.val < 175 then g32p_supplierForest_node_087254 else g32p_supplierForest_node_087318)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_087346 else g32p_supplierForest_node_087352) else (if i.val < 179 then g32p_supplierForest_node_087379 else g32p_supplierForest_node_087429)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_087464 else g32p_supplierForest_node_087490) else (if i.val < 183 then g32p_supplierForest_node_087514 else g32p_supplierForest_node_087586))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_087591 else g32p_supplierForest_node_087638) else (if i.val < 187 then g32p_supplierForest_node_087646 else g32p_supplierForest_node_087682)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_087858 else g32p_supplierForest_node_087880) else (if i.val < 191 then g32p_supplierForest_node_087910 else g32p_supplierForest_node_087919)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_087926 else g32p_supplierForest_node_087950) else (if i.val < 195 then g32p_supplierForest_node_088002 else g32p_supplierForest_node_088022)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_088044 else g32p_supplierForest_node_088163) else (if i.val < 199 then g32p_supplierForest_node_088215 else g32p_supplierForest_node_088235))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_088267 else g32p_supplierForest_node_088348) else (if i.val < 203 then g32p_supplierForest_node_088384 else g32p_supplierForest_node_088463)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_088520 else g32p_supplierForest_node_088567) else (if i.val < 207 then g32p_supplierForest_node_088651 else g32p_supplierForest_node_088689)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_088744 else g32p_supplierForest_node_088794) else (if i.val < 211 then g32p_supplierForest_node_088863 else g32p_supplierForest_node_088864)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_088889 else g32p_supplierForest_node_088944) else (if i.val < 215 then g32p_supplierForest_node_088953 else g32p_supplierForest_node_089000))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_089145 else g32p_supplierForest_node_089165) else (if i.val < 219 then g32p_supplierForest_node_089276 else g32p_supplierForest_node_089432)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_089515 else g32p_supplierForest_node_089521) else (if i.val < 223 then g32p_supplierForest_node_089545 else g32p_supplierForest_node_089580))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_089584 else g32p_supplierForest_node_089591) else (if i.val < 227 then g32p_supplierForest_node_089659 else g32p_supplierForest_node_089661)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_089685 else g32p_supplierForest_node_089799) else (if i.val < 231 then g32p_supplierForest_node_089852 else g32p_supplierForest_node_089934))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_089988 else g32p_supplierForest_node_090006) else (if i.val < 235 then g32p_supplierForest_node_090026 else g32p_supplierForest_node_090065)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_090069 else g32p_supplierForest_node_090168) else (if i.val < 239 then g32p_supplierForest_node_090195 else g32p_supplierForest_node_090200)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_090261 else g32p_supplierForest_node_090265) else (if i.val < 243 then g32p_supplierForest_node_090287 else g32p_supplierForest_node_090376)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_090463 else g32p_supplierForest_node_090524) else (if i.val < 247 then g32p_supplierForest_node_090543 else g32p_supplierForest_node_090629))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_090648 else g32p_supplierForest_node_090675) else (if i.val < 251 then g32p_supplierForest_node_090692 else g32p_supplierForest_node_090704)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_090707 else g32p_supplierForest_node_090735) else (if i.val < 255 then g32p_supplierForest_node_090828 else g32p_supplierForest_node_090886))))))))

def g32p_supplierForest_classes_137 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 54 else 49) else (if i.val < 3 then 26 else 25)) else (if i.val < 6 then (if i.val < 5 then 47 else 47) else (if i.val < 7 then 47 else 49))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 46 else 26) else (if i.val < 11 then 12 else 49)) else (if i.val < 14 then (if i.val < 13 then 47 else 54) else (if i.val < 15 then 49 else 46)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 55 else 46) else (if i.val < 19 then 25 else 9)) else (if i.val < 22 then (if i.val < 21 then 49 else 49) else (if i.val < 23 then 47 else 45))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 49 else 49) else (if i.val < 27 then 47 else 49)) else (if i.val < 30 then (if i.val < 29 then 49 else 49) else (if i.val < 31 then 26 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 55 else 46) else (if i.val < 35 then 46 else 46)) else (if i.val < 38 then (if i.val < 37 then 26 else 53) else (if i.val < 39 then 26 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 46 else 49) else (if i.val < 43 then 49 else 49)) else (if i.val < 46 then (if i.val < 45 then 46 else 49) else (if i.val < 47 then 49 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 49) else (if i.val < 51 then 46 else 46)) else (if i.val < 54 then (if i.val < 53 then 49 else 25) else (if i.val < 55 then 49 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 49) else (if i.val < 59 then 49 else 49)) else (if i.val < 62 then (if i.val < 61 then 46 else 49) else (if i.val < 63 then 49 else 49)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 50 else 49) else (if i.val < 67 then 55 else 49)) else (if i.val < 70 then (if i.val < 69 then 54 else 46) else (if i.val < 71 then 49 else 46))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 49) else (if i.val < 75 then 49 else 26)) else (if i.val < 78 then (if i.val < 77 then 49 else 49) else (if i.val < 79 then 46 else 49)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 52 else 49) else (if i.val < 83 then 49 else 49)) else (if i.val < 86 then (if i.val < 85 then 49 else 47) else (if i.val < 87 then 49 else 49))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 46) else (if i.val < 91 then 49 else 46)) else (if i.val < 94 then (if i.val < 93 then 49 else 46) else (if i.val < 95 then 49 else 46))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 49 else 46) else (if i.val < 99 then 49 else 49)) else (if i.val < 102 then (if i.val < 101 then 49 else 46) else (if i.val < 103 then 49 else 48))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 26 else 49) else (if i.val < 107 then 9 else 46)) else (if i.val < 110 then (if i.val < 109 then 47 else 46) else (if i.val < 111 then 49 else 47)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 49) else (if i.val < 115 then 26 else 26)) else (if i.val < 118 then (if i.val < 117 then 46 else 26) else (if i.val < 119 then 49 else 49))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 49 else 49) else (if i.val < 123 then 46 else 46)) else (if i.val < 126 then (if i.val < 125 then 83 else 49) else (if i.val < 127 then 46 else 53))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 80 else 46) else (if i.val < 131 then 55 else 47)) else (if i.val < 134 then (if i.val < 133 then 47 else 47) else (if i.val < 135 then 26 else 26))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 47 else 50) else (if i.val < 139 then 49 else 53)) else (if i.val < 142 then (if i.val < 141 then 49 else 47) else (if i.val < 143 then 46 else 46)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 47 else 46) else (if i.val < 147 then 46 else 46)) else (if i.val < 150 then (if i.val < 149 then 49 else 49) else (if i.val < 151 then 47 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 47 else 53) else (if i.val < 155 then 49 else 12)) else (if i.val < 158 then (if i.val < 157 then 49 else 49) else (if i.val < 159 then 47 else 46))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 55 else 47) else (if i.val < 163 then 49 else 47)) else (if i.val < 166 then (if i.val < 165 then 49 else 49) else (if i.val < 167 then 49 else 46))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 46 else 46) else (if i.val < 171 then 25 else 46)) else (if i.val < 174 then (if i.val < 173 then 49 else 49) else (if i.val < 175 then 47 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 46) else (if i.val < 179 then 49 else 26)) else (if i.val < 182 then (if i.val < 181 then 86 else 53) else (if i.val < 183 then 9 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 46 else 46) else (if i.val < 187 then 46 else 48)) else (if i.val < 190 then (if i.val < 189 then 47 else 49) else (if i.val < 191 then 49 else 50)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 50 else 49) else (if i.val < 195 then 50 else 53)) else (if i.val < 198 then (if i.val < 197 then 49 else 46) else (if i.val < 199 then 49 else 46))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 49 else 49) else (if i.val < 203 then 46 else 46)) else (if i.val < 206 then (if i.val < 205 then 46 else 49) else (if i.val < 207 then 46 else 26)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 46 else 54) else (if i.val < 211 then 26 else 53)) else (if i.val < 214 then (if i.val < 213 then 26 else 46) else (if i.val < 215 then 49 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 47 else 50) else (if i.val < 219 then 47 else 55)) else (if i.val < 222 then (if i.val < 221 then 54 else 9) else (if i.val < 223 then 49 else 49))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 49 else 27) else (if i.val < 227 then 49 else 54)) else (if i.val < 230 then (if i.val < 229 then 26 else 46) else (if i.val < 231 then 54 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 49 else 49) else (if i.val < 235 then 49 else 53)) else (if i.val < 238 then (if i.val < 237 then 49 else 49) else (if i.val < 239 then 50 else 26)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 49) else (if i.val < 243 then 49 else 50)) else (if i.val < 246 then (if i.val < 245 then 54 else 46) else (if i.val < 247 then 25 else 46))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 49) else (if i.val < 251 then 46 else 50)) else (if i.val < 254 then (if i.val < 253 then 49 else 49) else (if i.val < 255 then 26 else 46))))))))

theorem g32p_supplierForest_actual_137 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_137 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_137 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_078037
  · exact g32p_supplierForest_actual_078045
  · exact g32p_supplierForest_actual_078115
  · exact g32p_supplierForest_actual_078153
  · exact g32p_supplierForest_actual_078164
  · exact g32p_supplierForest_actual_078169
  · exact g32p_supplierForest_actual_078223
  · exact g32p_supplierForest_actual_078581
  · exact g32p_supplierForest_actual_078620
  · exact g32p_supplierForest_actual_078689
  · exact g32p_supplierForest_actual_078784
  · exact g32p_supplierForest_actual_078797
  · exact g32p_supplierForest_actual_078899
  · exact g32p_supplierForest_actual_078958
  · exact g32p_supplierForest_actual_078963
  · exact g32p_supplierForest_actual_078982
  · exact g32p_supplierForest_actual_079023
  · exact g32p_supplierForest_actual_079041
  · exact g32p_supplierForest_actual_079046
  · exact g32p_supplierForest_actual_079135
  · exact g32p_supplierForest_actual_079171
  · exact g32p_supplierForest_actual_079172
  · exact g32p_supplierForest_actual_079262
  · exact g32p_supplierForest_actual_079306
  · exact g32p_supplierForest_actual_079316
  · exact g32p_supplierForest_actual_079378
  · exact g32p_supplierForest_actual_079449
  · exact g32p_supplierForest_actual_079492
  · exact g32p_supplierForest_actual_079497
  · exact g32p_supplierForest_actual_079500
  · exact g32p_supplierForest_actual_079543
  · exact g32p_supplierForest_actual_079557
  · exact g32p_supplierForest_actual_079568
  · exact g32p_supplierForest_actual_079603
  · exact g32p_supplierForest_actual_079701
  · exact g32p_supplierForest_actual_079798
  · exact g32p_supplierForest_actual_079810
  · exact g32p_supplierForest_actual_079814
  · exact g32p_supplierForest_actual_079835
  · exact g32p_supplierForest_actual_079838
  · exact g32p_supplierForest_actual_079845
  · exact g32p_supplierForest_actual_079893
  · exact g32p_supplierForest_actual_079948
  · exact g32p_supplierForest_actual_080040
  · exact g32p_supplierForest_actual_080064
  · exact g32p_supplierForest_actual_080068
  · exact g32p_supplierForest_actual_080115
  · exact g32p_supplierForest_actual_080159
  · exact g32p_supplierForest_actual_080227
  · exact g32p_supplierForest_actual_080265
  · exact g32p_supplierForest_actual_080332
  · exact g32p_supplierForest_actual_080353
  · exact g32p_supplierForest_actual_080356
  · exact g32p_supplierForest_actual_080357
  · exact g32p_supplierForest_actual_080359
  · exact g32p_supplierForest_actual_080399
  · exact g32p_supplierForest_actual_080418
  · exact g32p_supplierForest_actual_080432
  · exact g32p_supplierForest_actual_080483
  · exact g32p_supplierForest_actual_080553
  · exact g32p_supplierForest_actual_080576
  · exact g32p_supplierForest_actual_080616
  · exact g32p_supplierForest_actual_080683
  · exact g32p_supplierForest_actual_080692
  · exact g32p_supplierForest_actual_080706
  · exact g32p_supplierForest_actual_080742
  · exact g32p_supplierForest_actual_080774
  · exact g32p_supplierForest_actual_080799
  · exact g32p_supplierForest_actual_080835
  · exact g32p_supplierForest_actual_080858
  · exact g32p_supplierForest_actual_080981
  · exact g32p_supplierForest_actual_081121
  · exact g32p_supplierForest_actual_081228
  · exact g32p_supplierForest_actual_081254
  · exact g32p_supplierForest_actual_081270
  · exact g32p_supplierForest_actual_081272
  · exact g32p_supplierForest_actual_081285
  · exact g32p_supplierForest_actual_081348
  · exact g32p_supplierForest_actual_081383
  · exact g32p_supplierForest_actual_081459
  · exact g32p_supplierForest_actual_081460
  · exact g32p_supplierForest_actual_081463
  · exact g32p_supplierForest_actual_081555
  · exact g32p_supplierForest_actual_081588
  · exact g32p_supplierForest_actual_081740
  · exact g32p_supplierForest_actual_081899
  · exact g32p_supplierForest_actual_081905
  · exact g32p_supplierForest_actual_081915
  · exact g32p_supplierForest_actual_082102
  · exact g32p_supplierForest_actual_082188
  · exact g32p_supplierForest_actual_082211
  · exact g32p_supplierForest_actual_082224
  · exact g32p_supplierForest_actual_082324
  · exact g32p_supplierForest_actual_082382
  · exact g32p_supplierForest_actual_082391
  · exact g32p_supplierForest_actual_082443
  · exact g32p_supplierForest_actual_082464
  · exact g32p_supplierForest_actual_082476
  · exact g32p_supplierForest_actual_082530
  · exact g32p_supplierForest_actual_082577
  · exact g32p_supplierForest_actual_082611
  · exact g32p_supplierForest_actual_082722
  · exact g32p_supplierForest_actual_082750
  · exact g32p_supplierForest_actual_083042
  · exact g32p_supplierForest_actual_083180
  · exact g32p_supplierForest_actual_083230
  · exact g32p_supplierForest_actual_083251
  · exact g32p_supplierForest_actual_083330
  · exact g32p_supplierForest_actual_083350
  · exact g32p_supplierForest_actual_083437
  · exact g32p_supplierForest_actual_083440
  · exact g32p_supplierForest_actual_083528
  · exact g32p_supplierForest_actual_083565
  · exact g32p_supplierForest_actual_083602
  · exact g32p_supplierForest_actual_083712
  · exact g32p_supplierForest_actual_083739
  · exact g32p_supplierForest_actual_083878
  · exact g32p_supplierForest_actual_083898
  · exact g32p_supplierForest_actual_084070
  · exact g32p_supplierForest_actual_084222
  · exact g32p_supplierForest_actual_084246
  · exact g32p_supplierForest_actual_084255
  · exact g32p_supplierForest_actual_084310
  · exact g32p_supplierForest_actual_084359
  · exact g32p_supplierForest_actual_084368
  · exact g32p_supplierForest_actual_084508
  · exact g32p_supplierForest_actual_084517
  · exact g32p_supplierForest_actual_084539
  · exact g32p_supplierForest_actual_084552
  · exact g32p_supplierForest_actual_084605
  · exact g32p_supplierForest_actual_084617
  · exact g32p_supplierForest_actual_084682
  · exact g32p_supplierForest_actual_084705
  · exact g32p_supplierForest_actual_084752
  · exact g32p_supplierForest_actual_084775
  · exact g32p_supplierForest_actual_084789
  · exact g32p_supplierForest_actual_084830
  · exact g32p_supplierForest_actual_084974
  · exact g32p_supplierForest_actual_085024
  · exact g32p_supplierForest_actual_085073
  · exact g32p_supplierForest_actual_085135
  · exact g32p_supplierForest_actual_085304
  · exact g32p_supplierForest_actual_085417
  · exact g32p_supplierForest_actual_085463
  · exact g32p_supplierForest_actual_085593
  · exact g32p_supplierForest_actual_085856
  · exact g32p_supplierForest_actual_085865
  · exact g32p_supplierForest_actual_085912
  · exact g32p_supplierForest_actual_085927
  · exact g32p_supplierForest_actual_086005
  · exact g32p_supplierForest_actual_086069
  · exact g32p_supplierForest_actual_086074
  · exact g32p_supplierForest_actual_086161
  · exact g32p_supplierForest_actual_086183
  · exact g32p_supplierForest_actual_086374
  · exact g32p_supplierForest_actual_086428
  · exact g32p_supplierForest_actual_086432
  · exact g32p_supplierForest_actual_086519
  · exact g32p_supplierForest_actual_086570
  · exact g32p_supplierForest_actual_086612
  · exact g32p_supplierForest_actual_086637
  · exact g32p_supplierForest_actual_086692
  · exact g32p_supplierForest_actual_086769
  · exact g32p_supplierForest_actual_086807
  · exact g32p_supplierForest_actual_086847
  · exact g32p_supplierForest_actual_086883
  · exact g32p_supplierForest_actual_087072
  · exact g32p_supplierForest_actual_087115
  · exact g32p_supplierForest_actual_087118
  · exact g32p_supplierForest_actual_087134
  · exact g32p_supplierForest_actual_087153
  · exact g32p_supplierForest_actual_087211
  · exact g32p_supplierForest_actual_087221
  · exact g32p_supplierForest_actual_087241
  · exact g32p_supplierForest_actual_087254
  · exact g32p_supplierForest_actual_087318
  · exact g32p_supplierForest_actual_087346
  · exact g32p_supplierForest_actual_087352
  · exact g32p_supplierForest_actual_087379
  · exact g32p_supplierForest_actual_087429
  · exact g32p_supplierForest_actual_087464
  · exact g32p_supplierForest_actual_087490
  · exact g32p_supplierForest_actual_087514
  · exact g32p_supplierForest_actual_087586
  · exact g32p_supplierForest_actual_087591
  · exact g32p_supplierForest_actual_087638
  · exact g32p_supplierForest_actual_087646
  · exact g32p_supplierForest_actual_087682
  · exact g32p_supplierForest_actual_087858
  · exact g32p_supplierForest_actual_087880
  · exact g32p_supplierForest_actual_087910
  · exact g32p_supplierForest_actual_087919
  · exact g32p_supplierForest_actual_087926
  · exact g32p_supplierForest_actual_087950
  · exact g32p_supplierForest_actual_088002
  · exact g32p_supplierForest_actual_088022
  · exact g32p_supplierForest_actual_088044
  · exact g32p_supplierForest_actual_088163
  · exact g32p_supplierForest_actual_088215
  · exact g32p_supplierForest_actual_088235
  · exact g32p_supplierForest_actual_088267
  · exact g32p_supplierForest_actual_088348
  · exact g32p_supplierForest_actual_088384
  · exact g32p_supplierForest_actual_088463
  · exact g32p_supplierForest_actual_088520
  · exact g32p_supplierForest_actual_088567
  · exact g32p_supplierForest_actual_088651
  · exact g32p_supplierForest_actual_088689
  · exact g32p_supplierForest_actual_088744
  · exact g32p_supplierForest_actual_088794
  · exact g32p_supplierForest_actual_088863
  · exact g32p_supplierForest_actual_088864
  · exact g32p_supplierForest_actual_088889
  · exact g32p_supplierForest_actual_088944
  · exact g32p_supplierForest_actual_088953
  · exact g32p_supplierForest_actual_089000
  · exact g32p_supplierForest_actual_089145
  · exact g32p_supplierForest_actual_089165
  · exact g32p_supplierForest_actual_089276
  · exact g32p_supplierForest_actual_089432
  · exact g32p_supplierForest_actual_089515
  · exact g32p_supplierForest_actual_089521
  · exact g32p_supplierForest_actual_089545
  · exact g32p_supplierForest_actual_089580
  · exact g32p_supplierForest_actual_089584
  · exact g32p_supplierForest_actual_089591
  · exact g32p_supplierForest_actual_089659
  · exact g32p_supplierForest_actual_089661
  · exact g32p_supplierForest_actual_089685
  · exact g32p_supplierForest_actual_089799
  · exact g32p_supplierForest_actual_089852
  · exact g32p_supplierForest_actual_089934
  · exact g32p_supplierForest_actual_089988
  · exact g32p_supplierForest_actual_090006
  · exact g32p_supplierForest_actual_090026
  · exact g32p_supplierForest_actual_090065
  · exact g32p_supplierForest_actual_090069
  · exact g32p_supplierForest_actual_090168
  · exact g32p_supplierForest_actual_090195
  · exact g32p_supplierForest_actual_090200
  · exact g32p_supplierForest_actual_090261
  · exact g32p_supplierForest_actual_090265
  · exact g32p_supplierForest_actual_090287
  · exact g32p_supplierForest_actual_090376
  · exact g32p_supplierForest_actual_090463
  · exact g32p_supplierForest_actual_090524
  · exact g32p_supplierForest_actual_090543
  · exact g32p_supplierForest_actual_090629
  · exact g32p_supplierForest_actual_090648
  · exact g32p_supplierForest_actual_090675
  · exact g32p_supplierForest_actual_090692
  · exact g32p_supplierForest_actual_090704
  · exact g32p_supplierForest_actual_090707
  · exact g32p_supplierForest_actual_090735
  · exact g32p_supplierForest_actual_090828
  · exact g32p_supplierForest_actual_090886

def g32p_supplierForest_nodes_138 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_090907 else g32p_supplierForest_node_090926) else (if i.val < 3 then g32p_supplierForest_node_091058 else g32p_supplierForest_node_091196)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_091225 else g32p_supplierForest_node_091246) else (if i.val < 7 then g32p_supplierForest_node_091275 else g32p_supplierForest_node_091326))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_091457 else g32p_supplierForest_node_091550) else (if i.val < 11 then g32p_supplierForest_node_091585 else g32p_supplierForest_node_091612)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_091722 else g32p_supplierForest_node_091826) else (if i.val < 15 then g32p_supplierForest_node_091852 else g32p_supplierForest_node_091873)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_091887 else g32p_supplierForest_node_091966) else (if i.val < 19 then g32p_supplierForest_node_091982 else g32p_supplierForest_node_092004)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_092097 else g32p_supplierForest_node_092128) else (if i.val < 23 then g32p_supplierForest_node_092174 else g32p_supplierForest_node_092217))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_092317 else g32p_supplierForest_node_092374) else (if i.val < 27 then g32p_supplierForest_node_092385 else g32p_supplierForest_node_092397)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_092422 else g32p_supplierForest_node_092504) else (if i.val < 31 then g32p_supplierForest_node_092607 else g32p_supplierForest_node_092700))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_092712 else g32p_supplierForest_node_092736) else (if i.val < 35 then g32p_supplierForest_node_092891 else g32p_supplierForest_node_092931)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_092972 else g32p_supplierForest_node_093071) else (if i.val < 39 then g32p_supplierForest_node_093079 else g32p_supplierForest_node_093146))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_093161 else g32p_supplierForest_node_093224) else (if i.val < 43 then g32p_supplierForest_node_093236 else g32p_supplierForest_node_093239)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_093304 else g32p_supplierForest_node_093333) else (if i.val < 47 then g32p_supplierForest_node_093383 else g32p_supplierForest_node_093397)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_093421 else g32p_supplierForest_node_093471) else (if i.val < 51 then g32p_supplierForest_node_093484 else g32p_supplierForest_node_093523)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_093554 else g32p_supplierForest_node_093578) else (if i.val < 55 then g32p_supplierForest_node_093614 else g32p_supplierForest_node_093676))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_093679 else g32p_supplierForest_node_093843) else (if i.val < 59 then g32p_supplierForest_node_093998 else g32p_supplierForest_node_094124)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_094148 else g32p_supplierForest_node_094166) else (if i.val < 63 then g32p_supplierForest_node_094277 else g32p_supplierForest_node_094379)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_094390 else g32p_supplierForest_node_094460) else (if i.val < 67 then g32p_supplierForest_node_094461 else g32p_supplierForest_node_094488)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_094695 else g32p_supplierForest_node_094758) else (if i.val < 71 then g32p_supplierForest_node_094989 else g32p_supplierForest_node_095017))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_095087 else g32p_supplierForest_node_095105) else (if i.val < 75 then g32p_supplierForest_node_095106 else g32p_supplierForest_node_095144)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_095308 else g32p_supplierForest_node_095401) else (if i.val < 79 then g32p_supplierForest_node_095456 else g32p_supplierForest_node_095470)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_095480 else g32p_supplierForest_node_095627) else (if i.val < 83 then g32p_supplierForest_node_095640 else g32p_supplierForest_node_095676)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_095768 else g32p_supplierForest_node_095889) else (if i.val < 87 then g32p_supplierForest_node_095927 else g32p_supplierForest_node_096020))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_096057 else g32p_supplierForest_node_096222) else (if i.val < 91 then g32p_supplierForest_node_096279 else g32p_supplierForest_node_096323)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_096366 else g32p_supplierForest_node_096487) else (if i.val < 95 then g32p_supplierForest_node_096587 else g32p_supplierForest_node_096600))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_096632 else g32p_supplierForest_node_096744) else (if i.val < 99 then g32p_supplierForest_node_096769 else g32p_supplierForest_node_096770)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_096792 else g32p_supplierForest_node_096850) else (if i.val < 103 then g32p_supplierForest_node_096964 else g32p_supplierForest_node_096969))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_097069 else g32p_supplierForest_node_097138) else (if i.val < 107 then g32p_supplierForest_node_097266 else g32p_supplierForest_node_097270)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_097291 else g32p_supplierForest_node_097326) else (if i.val < 111 then g32p_supplierForest_node_097356 else g32p_supplierForest_node_097413)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_097432 else g32p_supplierForest_node_097464) else (if i.val < 115 then g32p_supplierForest_node_097502 else g32p_supplierForest_node_097546)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_097556 else g32p_supplierForest_node_097560) else (if i.val < 119 then g32p_supplierForest_node_097636 else g32p_supplierForest_node_097659))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_097678 else g32p_supplierForest_node_097713) else (if i.val < 123 then g32p_supplierForest_node_097759 else g32p_supplierForest_node_097994)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_098029 else g32p_supplierForest_node_098097) else (if i.val < 127 then g32p_supplierForest_node_098201 else g32p_supplierForest_node_098253))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_098259 else g32p_supplierForest_node_098282) else (if i.val < 131 then g32p_supplierForest_node_098419 else g32p_supplierForest_node_098454)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_098510 else g32p_supplierForest_node_098572) else (if i.val < 135 then g32p_supplierForest_node_098727 else g32p_supplierForest_node_098780))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_098793 else g32p_supplierForest_node_098836) else (if i.val < 139 then g32p_supplierForest_node_098922 else g32p_supplierForest_node_098971)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_099152 else g32p_supplierForest_node_099204) else (if i.val < 143 then g32p_supplierForest_node_099218 else g32p_supplierForest_node_099289)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_099337 else g32p_supplierForest_node_099359) else (if i.val < 147 then g32p_supplierForest_node_099371 else g32p_supplierForest_node_099427)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_099488 else g32p_supplierForest_node_099501) else (if i.val < 151 then g32p_supplierForest_node_099610 else g32p_supplierForest_node_099855))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_099909 else g32p_supplierForest_node_099945) else (if i.val < 155 then g32p_supplierForest_node_099946 else g32p_supplierForest_node_100011)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_100135 else g32p_supplierForest_node_100146) else (if i.val < 159 then g32p_supplierForest_node_100164 else g32p_supplierForest_node_100180))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_100206 else g32p_supplierForest_node_100410) else (if i.val < 163 then g32p_supplierForest_node_100422 else g32p_supplierForest_node_100437)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_100448 else g32p_supplierForest_node_100485) else (if i.val < 167 then g32p_supplierForest_node_100521 else g32p_supplierForest_node_100538))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_100595 else g32p_supplierForest_node_100664) else (if i.val < 171 then g32p_supplierForest_node_100744 else g32p_supplierForest_node_100766)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_100828 else g32p_supplierForest_node_100875) else (if i.val < 175 then g32p_supplierForest_node_101005 else g32p_supplierForest_node_101056)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_101071 else g32p_supplierForest_node_101107) else (if i.val < 179 then g32p_supplierForest_node_101144 else g32p_supplierForest_node_101192)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_101293 else g32p_supplierForest_node_101343) else (if i.val < 183 then g32p_supplierForest_node_101369 else g32p_supplierForest_node_101497))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_101500 else g32p_supplierForest_node_101545) else (if i.val < 187 then g32p_supplierForest_node_101689 else g32p_supplierForest_node_101861)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_101880 else g32p_supplierForest_node_101885) else (if i.val < 191 then g32p_supplierForest_node_101906 else g32p_supplierForest_node_101988)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_102022 else g32p_supplierForest_node_102040) else (if i.val < 195 then g32p_supplierForest_node_102145 else g32p_supplierForest_node_102204)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_102288 else g32p_supplierForest_node_102333) else (if i.val < 199 then g32p_supplierForest_node_102371 else g32p_supplierForest_node_102618))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_102622 else g32p_supplierForest_node_102666) else (if i.val < 203 then g32p_supplierForest_node_102674 else g32p_supplierForest_node_102689)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_102730 else g32p_supplierForest_node_102777) else (if i.val < 207 then g32p_supplierForest_node_102824 else g32p_supplierForest_node_102830)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_102900 else g32p_supplierForest_node_103071) else (if i.val < 211 then g32p_supplierForest_node_103188 else g32p_supplierForest_node_103283)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_103429 else g32p_supplierForest_node_103493) else (if i.val < 215 then g32p_supplierForest_node_103511 else g32p_supplierForest_node_103549))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_103721 else g32p_supplierForest_node_103747) else (if i.val < 219 then g32p_supplierForest_node_103750 else g32p_supplierForest_node_103895)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_103934 else g32p_supplierForest_node_104078) else (if i.val < 223 then g32p_supplierForest_node_104085 else g32p_supplierForest_node_104113))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_104115 else g32p_supplierForest_node_104320) else (if i.val < 227 then g32p_supplierForest_node_104445 else g32p_supplierForest_node_104482)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_104622 else g32p_supplierForest_node_104650) else (if i.val < 231 then g32p_supplierForest_node_104702 else g32p_supplierForest_node_104799))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_104842 else g32p_supplierForest_node_104920) else (if i.val < 235 then g32p_supplierForest_node_104954 else g32p_supplierForest_node_104968)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_105195 else g32p_supplierForest_node_105259) else (if i.val < 239 then g32p_supplierForest_node_105437 else g32p_supplierForest_node_105501)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_105510 else g32p_supplierForest_node_105692) else (if i.val < 243 then g32p_supplierForest_node_105710 else g32p_supplierForest_node_105736)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_105804 else g32p_supplierForest_node_105820) else (if i.val < 247 then g32p_supplierForest_node_105821 else g32p_supplierForest_node_105832))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_105838 else g32p_supplierForest_node_106099) else (if i.val < 251 then g32p_supplierForest_node_106289 else g32p_supplierForest_node_106296)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_106303 else g32p_supplierForest_node_106396) else (if i.val < 255 then g32p_supplierForest_node_106400 else g32p_supplierForest_node_106411))))))))

def g32p_supplierForest_classes_138 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 47 else 26) else (if i.val < 3 then 49 else 46)) else (if i.val < 6 then (if i.val < 5 then 46 else 49) else (if i.val < 7 then 26 else 25))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 49 else 49) else (if i.val < 11 then 46 else 46)) else (if i.val < 14 then (if i.val < 13 then 50 else 49) else (if i.val < 15 then 49 else 46)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 49 else 49) else (if i.val < 19 then 46 else 49)) else (if i.val < 22 then (if i.val < 21 then 26 else 49) else (if i.val < 23 then 49 else 46))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 46 else 46) else (if i.val < 27 then 46 else 47)) else (if i.val < 30 then (if i.val < 29 then 12 else 46) else (if i.val < 31 then 46 else 46))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 46 else 49) else (if i.val < 35 then 49 else 49)) else (if i.val < 38 then (if i.val < 37 then 49 else 46) else (if i.val < 39 then 49 else 46))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 46 else 54) else (if i.val < 43 then 46 else 50)) else (if i.val < 46 then (if i.val < 45 then 46 else 46) else (if i.val < 47 then 46 else 49)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 46 else 49) else (if i.val < 51 then 53 else 26)) else (if i.val < 54 then (if i.val < 53 then 49 else 45) else (if i.val < 55 then 47 else 26))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 46 else 49) else (if i.val < 59 then 49 else 46)) else (if i.val < 62 then (if i.val < 61 then 46 else 49) else (if i.val < 63 then 49 else 9)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 26) else (if i.val < 67 then 49 else 46)) else (if i.val < 70 then (if i.val < 69 then 26 else 46) else (if i.val < 71 then 46 else 54))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 46 else 49) else (if i.val < 75 then 25 else 49)) else (if i.val < 78 then (if i.val < 77 then 47 else 46) else (if i.val < 79 then 80 else 49)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 46 else 49) else (if i.val < 83 then 46 else 49)) else (if i.val < 86 then (if i.val < 85 then 47 else 46) else (if i.val < 87 then 49 else 47))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 54 else 54) else (if i.val < 91 then 46 else 46)) else (if i.val < 94 then (if i.val < 93 then 46 else 49) else (if i.val < 95 then 46 else 26))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 49) else (if i.val < 99 then 49 else 46)) else (if i.val < 102 then (if i.val < 101 then 25 else 26) else (if i.val < 103 then 49 else 46))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 49 else 47) else (if i.val < 107 then 54 else 26)) else (if i.val < 110 then (if i.val < 109 then 53 else 49) else (if i.val < 111 then 47 else 46)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 49 else 45) else (if i.val < 115 then 25 else 47)) else (if i.val < 118 then (if i.val < 117 then 46 else 46) else (if i.val < 119 then 47 else 53))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 47 else 49) else (if i.val < 123 then 53 else 46)) else (if i.val < 126 then (if i.val < 125 then 49 else 46) else (if i.val < 127 then 46 else 49))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 47 else 49) else (if i.val < 131 then 49 else 46)) else (if i.val < 134 then (if i.val < 133 then 49 else 50) else (if i.val < 135 then 53 else 25))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 46) else (if i.val < 139 then 49 else 46)) else (if i.val < 142 then (if i.val < 141 then 49 else 54) else (if i.val < 143 then 25 else 26)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 49) else (if i.val < 147 then 49 else 49)) else (if i.val < 150 then (if i.val < 149 then 46 else 49) else (if i.val < 151 then 80 else 46))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 49 else 9) else (if i.val < 155 then 54 else 46)) else (if i.val < 158 then (if i.val < 157 then 49 else 46) else (if i.val < 159 then 46 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 47 else 49) else (if i.val < 163 then 46 else 49)) else (if i.val < 166 then (if i.val < 165 then 55 else 47) else (if i.val < 167 then 86 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 25 else 54) else (if i.val < 171 then 46 else 46)) else (if i.val < 174 then (if i.val < 173 then 54 else 49) else (if i.val < 175 then 49 else 86)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 53 else 46) else (if i.val < 179 then 49 else 49)) else (if i.val < 182 then (if i.val < 181 then 26 else 49) else (if i.val < 183 then 46 else 46))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 86) else (if i.val < 187 then 46 else 49)) else (if i.val < 190 then (if i.val < 189 then 46 else 49) else (if i.val < 191 then 57 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 36 else 57) else (if i.val < 195 then 16 else 59)) else (if i.val < 198 then (if i.val < 197 then 30 else 57) else (if i.val < 199 then 57 else 29))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 16 else 57) else (if i.val < 203 then 57 else 57)) else (if i.val < 206 then (if i.val < 205 then 57 else 57) else (if i.val < 207 then 30 else 36)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 59 else 66) else (if i.val < 211 then 30 else 57)) else (if i.val < 214 then (if i.val < 213 then 30 else 30) else (if i.val < 215 then 30 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 30 else 16) else (if i.val < 219 then 57 else 57)) else (if i.val < 222 then (if i.val < 221 then 30 else 57) else (if i.val < 223 then 57 else 63))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 30 else 57) else (if i.val < 227 then 57 else 57)) else (if i.val < 230 then (if i.val < 229 then 57 else 16) else (if i.val < 231 then 16 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 60) else (if i.val < 235 then 57 else 30)) else (if i.val < 238 then (if i.val < 237 then 57 else 36) else (if i.val < 239 then 57 else 57)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 57 else 35) else (if i.val < 243 then 30 else 57)) else (if i.val < 246 then (if i.val < 245 then 57 else 57) else (if i.val < 247 then 60 else 57))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 57 else 29) else (if i.val < 251 then 60 else 30)) else (if i.val < 254 then (if i.val < 253 then 29 else 57) else (if i.val < 255 then 57 else 60))))))))

theorem g32p_supplierForest_actual_138 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_138 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_138 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_090907
  · exact g32p_supplierForest_actual_090926
  · exact g32p_supplierForest_actual_091058
  · exact g32p_supplierForest_actual_091196
  · exact g32p_supplierForest_actual_091225
  · exact g32p_supplierForest_actual_091246
  · exact g32p_supplierForest_actual_091275
  · exact g32p_supplierForest_actual_091326
  · exact g32p_supplierForest_actual_091457
  · exact g32p_supplierForest_actual_091550
  · exact g32p_supplierForest_actual_091585
  · exact g32p_supplierForest_actual_091612
  · exact g32p_supplierForest_actual_091722
  · exact g32p_supplierForest_actual_091826
  · exact g32p_supplierForest_actual_091852
  · exact g32p_supplierForest_actual_091873
  · exact g32p_supplierForest_actual_091887
  · exact g32p_supplierForest_actual_091966
  · exact g32p_supplierForest_actual_091982
  · exact g32p_supplierForest_actual_092004
  · exact g32p_supplierForest_actual_092097
  · exact g32p_supplierForest_actual_092128
  · exact g32p_supplierForest_actual_092174
  · exact g32p_supplierForest_actual_092217
  · exact g32p_supplierForest_actual_092317
  · exact g32p_supplierForest_actual_092374
  · exact g32p_supplierForest_actual_092385
  · exact g32p_supplierForest_actual_092397
  · exact g32p_supplierForest_actual_092422
  · exact g32p_supplierForest_actual_092504
  · exact g32p_supplierForest_actual_092607
  · exact g32p_supplierForest_actual_092700
  · exact g32p_supplierForest_actual_092712
  · exact g32p_supplierForest_actual_092736
  · exact g32p_supplierForest_actual_092891
  · exact g32p_supplierForest_actual_092931
  · exact g32p_supplierForest_actual_092972
  · exact g32p_supplierForest_actual_093071
  · exact g32p_supplierForest_actual_093079
  · exact g32p_supplierForest_actual_093146
  · exact g32p_supplierForest_actual_093161
  · exact g32p_supplierForest_actual_093224
  · exact g32p_supplierForest_actual_093236
  · exact g32p_supplierForest_actual_093239
  · exact g32p_supplierForest_actual_093304
  · exact g32p_supplierForest_actual_093333
  · exact g32p_supplierForest_actual_093383
  · exact g32p_supplierForest_actual_093397
  · exact g32p_supplierForest_actual_093421
  · exact g32p_supplierForest_actual_093471
  · exact g32p_supplierForest_actual_093484
  · exact g32p_supplierForest_actual_093523
  · exact g32p_supplierForest_actual_093554
  · exact g32p_supplierForest_actual_093578
  · exact g32p_supplierForest_actual_093614
  · exact g32p_supplierForest_actual_093676
  · exact g32p_supplierForest_actual_093679
  · exact g32p_supplierForest_actual_093843
  · exact g32p_supplierForest_actual_093998
  · exact g32p_supplierForest_actual_094124
  · exact g32p_supplierForest_actual_094148
  · exact g32p_supplierForest_actual_094166
  · exact g32p_supplierForest_actual_094277
  · exact g32p_supplierForest_actual_094379
  · exact g32p_supplierForest_actual_094390
  · exact g32p_supplierForest_actual_094460
  · exact g32p_supplierForest_actual_094461
  · exact g32p_supplierForest_actual_094488
  · exact g32p_supplierForest_actual_094695
  · exact g32p_supplierForest_actual_094758
  · exact g32p_supplierForest_actual_094989
  · exact g32p_supplierForest_actual_095017
  · exact g32p_supplierForest_actual_095087
  · exact g32p_supplierForest_actual_095105
  · exact g32p_supplierForest_actual_095106
  · exact g32p_supplierForest_actual_095144
  · exact g32p_supplierForest_actual_095308
  · exact g32p_supplierForest_actual_095401
  · exact g32p_supplierForest_actual_095456
  · exact g32p_supplierForest_actual_095470
  · exact g32p_supplierForest_actual_095480
  · exact g32p_supplierForest_actual_095627
  · exact g32p_supplierForest_actual_095640
  · exact g32p_supplierForest_actual_095676
  · exact g32p_supplierForest_actual_095768
  · exact g32p_supplierForest_actual_095889
  · exact g32p_supplierForest_actual_095927
  · exact g32p_supplierForest_actual_096020
  · exact g32p_supplierForest_actual_096057
  · exact g32p_supplierForest_actual_096222
  · exact g32p_supplierForest_actual_096279
  · exact g32p_supplierForest_actual_096323
  · exact g32p_supplierForest_actual_096366
  · exact g32p_supplierForest_actual_096487
  · exact g32p_supplierForest_actual_096587
  · exact g32p_supplierForest_actual_096600
  · exact g32p_supplierForest_actual_096632
  · exact g32p_supplierForest_actual_096744
  · exact g32p_supplierForest_actual_096769
  · exact g32p_supplierForest_actual_096770
  · exact g32p_supplierForest_actual_096792
  · exact g32p_supplierForest_actual_096850
  · exact g32p_supplierForest_actual_096964
  · exact g32p_supplierForest_actual_096969
  · exact g32p_supplierForest_actual_097069
  · exact g32p_supplierForest_actual_097138
  · exact g32p_supplierForest_actual_097266
  · exact g32p_supplierForest_actual_097270
  · exact g32p_supplierForest_actual_097291
  · exact g32p_supplierForest_actual_097326
  · exact g32p_supplierForest_actual_097356
  · exact g32p_supplierForest_actual_097413
  · exact g32p_supplierForest_actual_097432
  · exact g32p_supplierForest_actual_097464
  · exact g32p_supplierForest_actual_097502
  · exact g32p_supplierForest_actual_097546
  · exact g32p_supplierForest_actual_097556
  · exact g32p_supplierForest_actual_097560
  · exact g32p_supplierForest_actual_097636
  · exact g32p_supplierForest_actual_097659
  · exact g32p_supplierForest_actual_097678
  · exact g32p_supplierForest_actual_097713
  · exact g32p_supplierForest_actual_097759
  · exact g32p_supplierForest_actual_097994
  · exact g32p_supplierForest_actual_098029
  · exact g32p_supplierForest_actual_098097
  · exact g32p_supplierForest_actual_098201
  · exact g32p_supplierForest_actual_098253
  · exact g32p_supplierForest_actual_098259
  · exact g32p_supplierForest_actual_098282
  · exact g32p_supplierForest_actual_098419
  · exact g32p_supplierForest_actual_098454
  · exact g32p_supplierForest_actual_098510
  · exact g32p_supplierForest_actual_098572
  · exact g32p_supplierForest_actual_098727
  · exact g32p_supplierForest_actual_098780
  · exact g32p_supplierForest_actual_098793
  · exact g32p_supplierForest_actual_098836
  · exact g32p_supplierForest_actual_098922
  · exact g32p_supplierForest_actual_098971
  · exact g32p_supplierForest_actual_099152
  · exact g32p_supplierForest_actual_099204
  · exact g32p_supplierForest_actual_099218
  · exact g32p_supplierForest_actual_099289
  · exact g32p_supplierForest_actual_099337
  · exact g32p_supplierForest_actual_099359
  · exact g32p_supplierForest_actual_099371
  · exact g32p_supplierForest_actual_099427
  · exact g32p_supplierForest_actual_099488
  · exact g32p_supplierForest_actual_099501
  · exact g32p_supplierForest_actual_099610
  · exact g32p_supplierForest_actual_099855
  · exact g32p_supplierForest_actual_099909
  · exact g32p_supplierForest_actual_099945
  · exact g32p_supplierForest_actual_099946
  · exact g32p_supplierForest_actual_100011
  · exact g32p_supplierForest_actual_100135
  · exact g32p_supplierForest_actual_100146
  · exact g32p_supplierForest_actual_100164
  · exact g32p_supplierForest_actual_100180
  · exact g32p_supplierForest_actual_100206
  · exact g32p_supplierForest_actual_100410
  · exact g32p_supplierForest_actual_100422
  · exact g32p_supplierForest_actual_100437
  · exact g32p_supplierForest_actual_100448
  · exact g32p_supplierForest_actual_100485
  · exact g32p_supplierForest_actual_100521
  · exact g32p_supplierForest_actual_100538
  · exact g32p_supplierForest_actual_100595
  · exact g32p_supplierForest_actual_100664
  · exact g32p_supplierForest_actual_100744
  · exact g32p_supplierForest_actual_100766
  · exact g32p_supplierForest_actual_100828
  · exact g32p_supplierForest_actual_100875
  · exact g32p_supplierForest_actual_101005
  · exact g32p_supplierForest_actual_101056
  · exact g32p_supplierForest_actual_101071
  · exact g32p_supplierForest_actual_101107
  · exact g32p_supplierForest_actual_101144
  · exact g32p_supplierForest_actual_101192
  · exact g32p_supplierForest_actual_101293
  · exact g32p_supplierForest_actual_101343
  · exact g32p_supplierForest_actual_101369
  · exact g32p_supplierForest_actual_101497
  · exact g32p_supplierForest_actual_101500
  · exact g32p_supplierForest_actual_101545
  · exact g32p_supplierForest_actual_101689
  · exact g32p_supplierForest_actual_101861
  · exact g32p_supplierForest_actual_101880
  · exact g32p_supplierForest_actual_101885
  · exact g32p_supplierForest_actual_101906
  · exact g32p_supplierForest_actual_101988
  · exact g32p_supplierForest_actual_102022
  · exact g32p_supplierForest_actual_102040
  · exact g32p_supplierForest_actual_102145
  · exact g32p_supplierForest_actual_102204
  · exact g32p_supplierForest_actual_102288
  · exact g32p_supplierForest_actual_102333
  · exact g32p_supplierForest_actual_102371
  · exact g32p_supplierForest_actual_102618
  · exact g32p_supplierForest_actual_102622
  · exact g32p_supplierForest_actual_102666
  · exact g32p_supplierForest_actual_102674
  · exact g32p_supplierForest_actual_102689
  · exact g32p_supplierForest_actual_102730
  · exact g32p_supplierForest_actual_102777
  · exact g32p_supplierForest_actual_102824
  · exact g32p_supplierForest_actual_102830
  · exact g32p_supplierForest_actual_102900
  · exact g32p_supplierForest_actual_103071
  · exact g32p_supplierForest_actual_103188
  · exact g32p_supplierForest_actual_103283
  · exact g32p_supplierForest_actual_103429
  · exact g32p_supplierForest_actual_103493
  · exact g32p_supplierForest_actual_103511
  · exact g32p_supplierForest_actual_103549
  · exact g32p_supplierForest_actual_103721
  · exact g32p_supplierForest_actual_103747
  · exact g32p_supplierForest_actual_103750
  · exact g32p_supplierForest_actual_103895
  · exact g32p_supplierForest_actual_103934
  · exact g32p_supplierForest_actual_104078
  · exact g32p_supplierForest_actual_104085
  · exact g32p_supplierForest_actual_104113
  · exact g32p_supplierForest_actual_104115
  · exact g32p_supplierForest_actual_104320
  · exact g32p_supplierForest_actual_104445
  · exact g32p_supplierForest_actual_104482
  · exact g32p_supplierForest_actual_104622
  · exact g32p_supplierForest_actual_104650
  · exact g32p_supplierForest_actual_104702
  · exact g32p_supplierForest_actual_104799
  · exact g32p_supplierForest_actual_104842
  · exact g32p_supplierForest_actual_104920
  · exact g32p_supplierForest_actual_104954
  · exact g32p_supplierForest_actual_104968
  · exact g32p_supplierForest_actual_105195
  · exact g32p_supplierForest_actual_105259
  · exact g32p_supplierForest_actual_105437
  · exact g32p_supplierForest_actual_105501
  · exact g32p_supplierForest_actual_105510
  · exact g32p_supplierForest_actual_105692
  · exact g32p_supplierForest_actual_105710
  · exact g32p_supplierForest_actual_105736
  · exact g32p_supplierForest_actual_105804
  · exact g32p_supplierForest_actual_105820
  · exact g32p_supplierForest_actual_105821
  · exact g32p_supplierForest_actual_105832
  · exact g32p_supplierForest_actual_105838
  · exact g32p_supplierForest_actual_106099
  · exact g32p_supplierForest_actual_106289
  · exact g32p_supplierForest_actual_106296
  · exact g32p_supplierForest_actual_106303
  · exact g32p_supplierForest_actual_106396
  · exact g32p_supplierForest_actual_106400
  · exact g32p_supplierForest_actual_106411

def g32p_supplierForest_nodes_139 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_106418 else g32p_supplierForest_node_106421) else (if i.val < 3 then g32p_supplierForest_node_106595 else g32p_supplierForest_node_106602)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_106624 else g32p_supplierForest_node_106795) else (if i.val < 7 then g32p_supplierForest_node_106878 else g32p_supplierForest_node_106917))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_106982 else g32p_supplierForest_node_107036) else (if i.val < 11 then g32p_supplierForest_node_107197 else g32p_supplierForest_node_107293)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_107381 else g32p_supplierForest_node_107495) else (if i.val < 15 then g32p_supplierForest_node_107574 else g32p_supplierForest_node_107576)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_107597 else g32p_supplierForest_node_107599) else (if i.val < 19 then g32p_supplierForest_node_107602 else g32p_supplierForest_node_107651)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_107689 else g32p_supplierForest_node_107863) else (if i.val < 23 then g32p_supplierForest_node_107911 else g32p_supplierForest_node_108268))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_108437 else g32p_supplierForest_node_108458) else (if i.val < 27 then g32p_supplierForest_node_108585 else g32p_supplierForest_node_108733)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_108886 else g32p_supplierForest_node_108917) else (if i.val < 31 then g32p_supplierForest_node_108967 else g32p_supplierForest_node_108969))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_108975 else g32p_supplierForest_node_109071) else (if i.val < 35 then g32p_supplierForest_node_109090 else g32p_supplierForest_node_109183)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_109287 else g32p_supplierForest_node_109329) else (if i.val < 39 then g32p_supplierForest_node_109425 else g32p_supplierForest_node_109521))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_109570 else g32p_supplierForest_node_109635) else (if i.val < 43 then g32p_supplierForest_node_109657 else g32p_supplierForest_node_109661)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_109681 else g32p_supplierForest_node_109821) else (if i.val < 47 then g32p_supplierForest_node_109891 else g32p_supplierForest_node_110027)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_110287 else g32p_supplierForest_node_110317) else (if i.val < 51 then g32p_supplierForest_node_110337 else g32p_supplierForest_node_110420)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_110432 else g32p_supplierForest_node_110469) else (if i.val < 55 then g32p_supplierForest_node_110471 else g32p_supplierForest_node_110487))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_110527 else g32p_supplierForest_node_110578) else (if i.val < 59 then g32p_supplierForest_node_110622 else g32p_supplierForest_node_110638)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_110693 else g32p_supplierForest_node_110696) else (if i.val < 63 then g32p_supplierForest_node_110753 else g32p_supplierForest_node_110782)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_110862 else g32p_supplierForest_node_110928) else (if i.val < 67 then g32p_supplierForest_node_110981 else g32p_supplierForest_node_110995)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_111019 else g32p_supplierForest_node_111068) else (if i.val < 71 then g32p_supplierForest_node_111079 else g32p_supplierForest_node_111128))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_111258 else g32p_supplierForest_node_111286) else (if i.val < 75 then g32p_supplierForest_node_111502 else g32p_supplierForest_node_111562)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_111607 else g32p_supplierForest_node_111662) else (if i.val < 79 then g32p_supplierForest_node_111737 else g32p_supplierForest_node_111762)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_112076 else g32p_supplierForest_node_112232) else (if i.val < 83 then g32p_supplierForest_node_112238 else g32p_supplierForest_node_112298)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_112310 else g32p_supplierForest_node_112327) else (if i.val < 87 then g32p_supplierForest_node_112334 else g32p_supplierForest_node_112350))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_112351 else g32p_supplierForest_node_112353) else (if i.val < 91 then g32p_supplierForest_node_112370 else g32p_supplierForest_node_112505)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_112523 else g32p_supplierForest_node_112575) else (if i.val < 95 then g32p_supplierForest_node_112625 else g32p_supplierForest_node_112728))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_112907 else g32p_supplierForest_node_112957) else (if i.val < 99 then g32p_supplierForest_node_112991 else g32p_supplierForest_node_113041)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_113255 else g32p_supplierForest_node_113266) else (if i.val < 103 then g32p_supplierForest_node_113504 else g32p_supplierForest_node_113528))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_113737 else g32p_supplierForest_node_113738) else (if i.val < 107 then g32p_supplierForest_node_113777 else g32p_supplierForest_node_113789)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_113817 else g32p_supplierForest_node_113954) else (if i.val < 111 then g32p_supplierForest_node_114050 else g32p_supplierForest_node_114103)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_114128 else g32p_supplierForest_node_114152) else (if i.val < 115 then g32p_supplierForest_node_114171 else g32p_supplierForest_node_114207)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_114323 else g32p_supplierForest_node_114326) else (if i.val < 119 then g32p_supplierForest_node_114565 else g32p_supplierForest_node_114600))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_114609 else g32p_supplierForest_node_114695) else (if i.val < 123 then g32p_supplierForest_node_114733 else g32p_supplierForest_node_114841)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_114847 else g32p_supplierForest_node_114849) else (if i.val < 127 then g32p_supplierForest_node_114939 else g32p_supplierForest_node_115016))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_115073 else g32p_supplierForest_node_115078) else (if i.val < 131 then g32p_supplierForest_node_115127 else g32p_supplierForest_node_115131)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_115168 else g32p_supplierForest_node_115173) else (if i.val < 135 then g32p_supplierForest_node_115179 else g32p_supplierForest_node_115192))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_115226 else g32p_supplierForest_node_115256) else (if i.val < 139 then g32p_supplierForest_node_115360 else g32p_supplierForest_node_115373)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_115376 else g32p_supplierForest_node_115435) else (if i.val < 143 then g32p_supplierForest_node_115459 else g32p_supplierForest_node_115528)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_115549 else g32p_supplierForest_node_115556) else (if i.val < 147 then g32p_supplierForest_node_115752 else g32p_supplierForest_node_115968)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_116010 else g32p_supplierForest_node_116086) else (if i.val < 151 then g32p_supplierForest_node_116127 else g32p_supplierForest_node_116142))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_116172 else g32p_supplierForest_node_116262) else (if i.val < 155 then g32p_supplierForest_node_116339 else g32p_supplierForest_node_116350)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_116524 else g32p_supplierForest_node_116529) else (if i.val < 159 then g32p_supplierForest_node_116653 else g32p_supplierForest_node_116667))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_116672 else g32p_supplierForest_node_116755) else (if i.val < 163 then g32p_supplierForest_node_116844 else g32p_supplierForest_node_116949)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_116954 else g32p_supplierForest_node_116968) else (if i.val < 167 then g32p_supplierForest_node_116982 else g32p_supplierForest_node_116996))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_117031 else g32p_supplierForest_node_117047) else (if i.val < 171 then g32p_supplierForest_node_117071 else g32p_supplierForest_node_117084)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_117153 else g32p_supplierForest_node_117202) else (if i.val < 175 then g32p_supplierForest_node_117310 else g32p_supplierForest_node_117364)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_117411 else g32p_supplierForest_node_117423) else (if i.val < 179 then g32p_supplierForest_node_117474 else g32p_supplierForest_node_117537)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_117579 else g32p_supplierForest_node_117665) else (if i.val < 183 then g32p_supplierForest_node_117773 else g32p_supplierForest_node_117832))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_117854 else g32p_supplierForest_node_117860) else (if i.val < 187 then g32p_supplierForest_node_117950 else g32p_supplierForest_node_117981)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_117994 else g32p_supplierForest_node_118069) else (if i.val < 191 then g32p_supplierForest_node_118071 else g32p_supplierForest_node_118085)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_118089 else g32p_supplierForest_node_118205) else (if i.val < 195 then g32p_supplierForest_node_118224 else g32p_supplierForest_node_118261)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_118315 else g32p_supplierForest_node_118329) else (if i.val < 199 then g32p_supplierForest_node_118528 else g32p_supplierForest_node_118605))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_118621 else g32p_supplierForest_node_118630) else (if i.val < 203 then g32p_supplierForest_node_118705 else g32p_supplierForest_node_118720)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_118813 else g32p_supplierForest_node_118883) else (if i.val < 207 then g32p_supplierForest_node_118887 else g32p_supplierForest_node_118920)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_118942 else g32p_supplierForest_node_118991) else (if i.val < 211 then g32p_supplierForest_node_118994 else g32p_supplierForest_node_119075)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_119110 else g32p_supplierForest_node_119243) else (if i.val < 215 then g32p_supplierForest_node_119307 else g32p_supplierForest_node_119495))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_119509 else g32p_supplierForest_node_119647) else (if i.val < 219 then g32p_supplierForest_node_119690 else g32p_supplierForest_node_119701)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_119767 else g32p_supplierForest_node_119831) else (if i.val < 223 then g32p_supplierForest_node_120022 else g32p_supplierForest_node_120098))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_120152 else g32p_supplierForest_node_120172) else (if i.val < 227 then g32p_supplierForest_node_120196 else g32p_supplierForest_node_120395)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_120522 else g32p_supplierForest_node_120614) else (if i.val < 231 then g32p_supplierForest_node_120667 else g32p_supplierForest_node_120725))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_120896 else g32p_supplierForest_node_120917) else (if i.val < 235 then g32p_supplierForest_node_120998 else g32p_supplierForest_node_121005)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_121041 else g32p_supplierForest_node_121102) else (if i.val < 239 then g32p_supplierForest_node_121123 else g32p_supplierForest_node_121154)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_121170 else g32p_supplierForest_node_121176) else (if i.val < 243 then g32p_supplierForest_node_121183 else g32p_supplierForest_node_121303)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_121363 else g32p_supplierForest_node_121367) else (if i.val < 247 then g32p_supplierForest_node_121433 else g32p_supplierForest_node_121439))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_121478 else g32p_supplierForest_node_121486) else (if i.val < 251 then g32p_supplierForest_node_121491 else g32p_supplierForest_node_121547)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_121561 else g32p_supplierForest_node_121663) else (if i.val < 255 then g32p_supplierForest_node_121707 else g32p_supplierForest_node_121751))))))))

def g32p_supplierForest_classes_139 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 60) else (if i.val < 3 then 60 else 57)) else (if i.val < 6 then (if i.val < 5 then 33 else 59) else (if i.val < 7 then 57 else 57))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 15 else 57) else (if i.val < 11 then 30 else 57)) else (if i.val < 14 then (if i.val < 13 then 30 else 57) else (if i.val < 15 then 30 else 30)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 60 else 60) else (if i.val < 19 then 57 else 33)) else (if i.val < 22 then (if i.val < 21 then 60 else 57) else (if i.val < 23 then 60 else 30))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 30 else 60) else (if i.val < 27 then 57 else 30)) else (if i.val < 30 then (if i.val < 29 then 30 else 63) else (if i.val < 31 then 57 else 59))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 30 else 60) else (if i.val < 35 then 30 else 57)) else (if i.val < 38 then (if i.val < 37 then 30 else 57) else (if i.val < 39 then 30 else 57))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 16 else 57) else (if i.val < 43 then 62 else 57)) else (if i.val < 46 then (if i.val < 45 then 36 else 16) else (if i.val < 47 then 60 else 57)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 30 else 66) else (if i.val < 51 then 62 else 30)) else (if i.val < 54 then (if i.val < 53 then 57 else 57) else (if i.val < 55 then 57 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 57 else 57) else (if i.val < 59 then 60 else 57)) else (if i.val < 62 then (if i.val < 61 then 30 else 30) else (if i.val < 63 then 57 else 59)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 57 else 29) else (if i.val < 67 then 57 else 57)) else (if i.val < 70 then (if i.val < 69 then 57 else 57) else (if i.val < 71 then 60 else 59))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 59 else 15) else (if i.val < 75 then 57 else 57)) else (if i.val < 78 then (if i.val < 77 then 57 else 57) else (if i.val < 79 then 57 else 60)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 57 else 61) else (if i.val < 83 then 66 else 30)) else (if i.val < 86 then (if i.val < 85 then 16 else 30) else (if i.val < 87 then 57 else 66))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 57 else 59) else (if i.val < 91 then 57 else 59)) else (if i.val < 94 then (if i.val < 93 then 57 else 57) else (if i.val < 95 then 60 else 57))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 60 else 63) else (if i.val < 99 then 62 else 59)) else (if i.val < 102 then (if i.val < 101 then 57 else 30) else (if i.val < 103 then 62 else 57))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 29 else 29) else (if i.val < 107 then 30 else 60)) else (if i.val < 110 then (if i.val < 109 then 30 else 60) else (if i.val < 111 then 63 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 57 else 30) else (if i.val < 115 then 30 else 57)) else (if i.val < 118 then (if i.val < 117 then 57 else 66) else (if i.val < 119 then 57 else 57))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 30 else 57) else (if i.val < 123 then 30 else 57)) else (if i.val < 126 then (if i.val < 125 then 36 else 57) else (if i.val < 127 then 30 else 16))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 16 else 30) else (if i.val < 131 then 57 else 57)) else (if i.val < 134 then (if i.val < 133 then 30 else 57) else (if i.val < 135 then 16 else 57))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 60 else 59) else (if i.val < 139 then 30 else 29)) else (if i.val < 142 then (if i.val < 141 then 62 else 14) else (if i.val < 143 then 57 else 30)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 60 else 57) else (if i.val < 147 then 60 else 57)) else (if i.val < 150 then (if i.val < 149 then 29 else 57) else (if i.val < 151 then 57 else 58))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 30 else 57) else (if i.val < 155 then 57 else 57)) else (if i.val < 158 then (if i.val < 157 then 57 else 58) else (if i.val < 159 then 58 else 60))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 57 else 57) else (if i.val < 163 then 30 else 57)) else (if i.val < 166 then (if i.val < 165 then 57 else 57) else (if i.val < 167 then 57 else 36))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 30 else 57) else (if i.val < 171 then 57 else 60)) else (if i.val < 174 then (if i.val < 173 then 63 else 66) else (if i.val < 175 then 57 else 30)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 57) else (if i.val < 179 then 30 else 30)) else (if i.val < 182 then (if i.val < 181 then 60 else 57) else (if i.val < 183 then 60 else 30))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 57) else (if i.val < 187 then 30 else 30)) else (if i.val < 190 then (if i.val < 189 then 30 else 57) else (if i.val < 191 then 30 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 57 else 60) else (if i.val < 195 then 57 else 57)) else (if i.val < 198 then (if i.val < 197 then 60 else 57) else (if i.val < 199 then 30 else 57))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 64 else 17) else (if i.val < 203 then 16 else 57)) else (if i.val < 206 then (if i.val < 205 then 30 else 57) else (if i.val < 207 then 57 else 57)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 16 else 57) else (if i.val < 211 then 57 else 57)) else (if i.val < 214 then (if i.val < 213 then 57 else 66) else (if i.val < 215 then 57 else 66))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 29 else 57) else (if i.val < 219 then 29 else 57)) else (if i.val < 222 then (if i.val < 221 then 62 else 57) else (if i.val < 223 then 60 else 30))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 66 else 57) else (if i.val < 227 then 16 else 60)) else (if i.val < 230 then (if i.val < 229 then 63 else 16) else (if i.val < 231 then 29 else 57))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 57 else 57) else (if i.val < 235 then 29 else 57)) else (if i.val < 238 then (if i.val < 237 then 60 else 57) else (if i.val < 239 then 63 else 30)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 62 else 33) else (if i.val < 243 then 60 else 30)) else (if i.val < 246 then (if i.val < 245 then 57 else 57) else (if i.val < 247 then 57 else 60))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 29 else 57) else (if i.val < 251 then 57 else 61)) else (if i.val < 254 then (if i.val < 253 then 57 else 16) else (if i.val < 255 then 57 else 30))))))))

theorem g32p_supplierForest_actual_139 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_139 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_139 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_106418
  · exact g32p_supplierForest_actual_106421
  · exact g32p_supplierForest_actual_106595
  · exact g32p_supplierForest_actual_106602
  · exact g32p_supplierForest_actual_106624
  · exact g32p_supplierForest_actual_106795
  · exact g32p_supplierForest_actual_106878
  · exact g32p_supplierForest_actual_106917
  · exact g32p_supplierForest_actual_106982
  · exact g32p_supplierForest_actual_107036
  · exact g32p_supplierForest_actual_107197
  · exact g32p_supplierForest_actual_107293
  · exact g32p_supplierForest_actual_107381
  · exact g32p_supplierForest_actual_107495
  · exact g32p_supplierForest_actual_107574
  · exact g32p_supplierForest_actual_107576
  · exact g32p_supplierForest_actual_107597
  · exact g32p_supplierForest_actual_107599
  · exact g32p_supplierForest_actual_107602
  · exact g32p_supplierForest_actual_107651
  · exact g32p_supplierForest_actual_107689
  · exact g32p_supplierForest_actual_107863
  · exact g32p_supplierForest_actual_107911
  · exact g32p_supplierForest_actual_108268
  · exact g32p_supplierForest_actual_108437
  · exact g32p_supplierForest_actual_108458
  · exact g32p_supplierForest_actual_108585
  · exact g32p_supplierForest_actual_108733
  · exact g32p_supplierForest_actual_108886
  · exact g32p_supplierForest_actual_108917
  · exact g32p_supplierForest_actual_108967
  · exact g32p_supplierForest_actual_108969
  · exact g32p_supplierForest_actual_108975
  · exact g32p_supplierForest_actual_109071
  · exact g32p_supplierForest_actual_109090
  · exact g32p_supplierForest_actual_109183
  · exact g32p_supplierForest_actual_109287
  · exact g32p_supplierForest_actual_109329
  · exact g32p_supplierForest_actual_109425
  · exact g32p_supplierForest_actual_109521
  · exact g32p_supplierForest_actual_109570
  · exact g32p_supplierForest_actual_109635
  · exact g32p_supplierForest_actual_109657
  · exact g32p_supplierForest_actual_109661
  · exact g32p_supplierForest_actual_109681
  · exact g32p_supplierForest_actual_109821
  · exact g32p_supplierForest_actual_109891
  · exact g32p_supplierForest_actual_110027
  · exact g32p_supplierForest_actual_110287
  · exact g32p_supplierForest_actual_110317
  · exact g32p_supplierForest_actual_110337
  · exact g32p_supplierForest_actual_110420
  · exact g32p_supplierForest_actual_110432
  · exact g32p_supplierForest_actual_110469
  · exact g32p_supplierForest_actual_110471
  · exact g32p_supplierForest_actual_110487
  · exact g32p_supplierForest_actual_110527
  · exact g32p_supplierForest_actual_110578
  · exact g32p_supplierForest_actual_110622
  · exact g32p_supplierForest_actual_110638
  · exact g32p_supplierForest_actual_110693
  · exact g32p_supplierForest_actual_110696
  · exact g32p_supplierForest_actual_110753
  · exact g32p_supplierForest_actual_110782
  · exact g32p_supplierForest_actual_110862
  · exact g32p_supplierForest_actual_110928
  · exact g32p_supplierForest_actual_110981
  · exact g32p_supplierForest_actual_110995
  · exact g32p_supplierForest_actual_111019
  · exact g32p_supplierForest_actual_111068
  · exact g32p_supplierForest_actual_111079
  · exact g32p_supplierForest_actual_111128
  · exact g32p_supplierForest_actual_111258
  · exact g32p_supplierForest_actual_111286
  · exact g32p_supplierForest_actual_111502
  · exact g32p_supplierForest_actual_111562
  · exact g32p_supplierForest_actual_111607
  · exact g32p_supplierForest_actual_111662
  · exact g32p_supplierForest_actual_111737
  · exact g32p_supplierForest_actual_111762
  · exact g32p_supplierForest_actual_112076
  · exact g32p_supplierForest_actual_112232
  · exact g32p_supplierForest_actual_112238
  · exact g32p_supplierForest_actual_112298
  · exact g32p_supplierForest_actual_112310
  · exact g32p_supplierForest_actual_112327
  · exact g32p_supplierForest_actual_112334
  · exact g32p_supplierForest_actual_112350
  · exact g32p_supplierForest_actual_112351
  · exact g32p_supplierForest_actual_112353
  · exact g32p_supplierForest_actual_112370
  · exact g32p_supplierForest_actual_112505
  · exact g32p_supplierForest_actual_112523
  · exact g32p_supplierForest_actual_112575
  · exact g32p_supplierForest_actual_112625
  · exact g32p_supplierForest_actual_112728
  · exact g32p_supplierForest_actual_112907
  · exact g32p_supplierForest_actual_112957
  · exact g32p_supplierForest_actual_112991
  · exact g32p_supplierForest_actual_113041
  · exact g32p_supplierForest_actual_113255
  · exact g32p_supplierForest_actual_113266
  · exact g32p_supplierForest_actual_113504
  · exact g32p_supplierForest_actual_113528
  · exact g32p_supplierForest_actual_113737
  · exact g32p_supplierForest_actual_113738
  · exact g32p_supplierForest_actual_113777
  · exact g32p_supplierForest_actual_113789
  · exact g32p_supplierForest_actual_113817
  · exact g32p_supplierForest_actual_113954
  · exact g32p_supplierForest_actual_114050
  · exact g32p_supplierForest_actual_114103
  · exact g32p_supplierForest_actual_114128
  · exact g32p_supplierForest_actual_114152
  · exact g32p_supplierForest_actual_114171
  · exact g32p_supplierForest_actual_114207
  · exact g32p_supplierForest_actual_114323
  · exact g32p_supplierForest_actual_114326
  · exact g32p_supplierForest_actual_114565
  · exact g32p_supplierForest_actual_114600
  · exact g32p_supplierForest_actual_114609
  · exact g32p_supplierForest_actual_114695
  · exact g32p_supplierForest_actual_114733
  · exact g32p_supplierForest_actual_114841
  · exact g32p_supplierForest_actual_114847
  · exact g32p_supplierForest_actual_114849
  · exact g32p_supplierForest_actual_114939
  · exact g32p_supplierForest_actual_115016
  · exact g32p_supplierForest_actual_115073
  · exact g32p_supplierForest_actual_115078
  · exact g32p_supplierForest_actual_115127
  · exact g32p_supplierForest_actual_115131
  · exact g32p_supplierForest_actual_115168
  · exact g32p_supplierForest_actual_115173
  · exact g32p_supplierForest_actual_115179
  · exact g32p_supplierForest_actual_115192
  · exact g32p_supplierForest_actual_115226
  · exact g32p_supplierForest_actual_115256
  · exact g32p_supplierForest_actual_115360
  · exact g32p_supplierForest_actual_115373
  · exact g32p_supplierForest_actual_115376
  · exact g32p_supplierForest_actual_115435
  · exact g32p_supplierForest_actual_115459
  · exact g32p_supplierForest_actual_115528
  · exact g32p_supplierForest_actual_115549
  · exact g32p_supplierForest_actual_115556
  · exact g32p_supplierForest_actual_115752
  · exact g32p_supplierForest_actual_115968
  · exact g32p_supplierForest_actual_116010
  · exact g32p_supplierForest_actual_116086
  · exact g32p_supplierForest_actual_116127
  · exact g32p_supplierForest_actual_116142
  · exact g32p_supplierForest_actual_116172
  · exact g32p_supplierForest_actual_116262
  · exact g32p_supplierForest_actual_116339
  · exact g32p_supplierForest_actual_116350
  · exact g32p_supplierForest_actual_116524
  · exact g32p_supplierForest_actual_116529
  · exact g32p_supplierForest_actual_116653
  · exact g32p_supplierForest_actual_116667
  · exact g32p_supplierForest_actual_116672
  · exact g32p_supplierForest_actual_116755
  · exact g32p_supplierForest_actual_116844
  · exact g32p_supplierForest_actual_116949
  · exact g32p_supplierForest_actual_116954
  · exact g32p_supplierForest_actual_116968
  · exact g32p_supplierForest_actual_116982
  · exact g32p_supplierForest_actual_116996
  · exact g32p_supplierForest_actual_117031
  · exact g32p_supplierForest_actual_117047
  · exact g32p_supplierForest_actual_117071
  · exact g32p_supplierForest_actual_117084
  · exact g32p_supplierForest_actual_117153
  · exact g32p_supplierForest_actual_117202
  · exact g32p_supplierForest_actual_117310
  · exact g32p_supplierForest_actual_117364
  · exact g32p_supplierForest_actual_117411
  · exact g32p_supplierForest_actual_117423
  · exact g32p_supplierForest_actual_117474
  · exact g32p_supplierForest_actual_117537
  · exact g32p_supplierForest_actual_117579
  · exact g32p_supplierForest_actual_117665
  · exact g32p_supplierForest_actual_117773
  · exact g32p_supplierForest_actual_117832
  · exact g32p_supplierForest_actual_117854
  · exact g32p_supplierForest_actual_117860
  · exact g32p_supplierForest_actual_117950
  · exact g32p_supplierForest_actual_117981
  · exact g32p_supplierForest_actual_117994
  · exact g32p_supplierForest_actual_118069
  · exact g32p_supplierForest_actual_118071
  · exact g32p_supplierForest_actual_118085
  · exact g32p_supplierForest_actual_118089
  · exact g32p_supplierForest_actual_118205
  · exact g32p_supplierForest_actual_118224
  · exact g32p_supplierForest_actual_118261
  · exact g32p_supplierForest_actual_118315
  · exact g32p_supplierForest_actual_118329
  · exact g32p_supplierForest_actual_118528
  · exact g32p_supplierForest_actual_118605
  · exact g32p_supplierForest_actual_118621
  · exact g32p_supplierForest_actual_118630
  · exact g32p_supplierForest_actual_118705
  · exact g32p_supplierForest_actual_118720
  · exact g32p_supplierForest_actual_118813
  · exact g32p_supplierForest_actual_118883
  · exact g32p_supplierForest_actual_118887
  · exact g32p_supplierForest_actual_118920
  · exact g32p_supplierForest_actual_118942
  · exact g32p_supplierForest_actual_118991
  · exact g32p_supplierForest_actual_118994
  · exact g32p_supplierForest_actual_119075
  · exact g32p_supplierForest_actual_119110
  · exact g32p_supplierForest_actual_119243
  · exact g32p_supplierForest_actual_119307
  · exact g32p_supplierForest_actual_119495
  · exact g32p_supplierForest_actual_119509
  · exact g32p_supplierForest_actual_119647
  · exact g32p_supplierForest_actual_119690
  · exact g32p_supplierForest_actual_119701
  · exact g32p_supplierForest_actual_119767
  · exact g32p_supplierForest_actual_119831
  · exact g32p_supplierForest_actual_120022
  · exact g32p_supplierForest_actual_120098
  · exact g32p_supplierForest_actual_120152
  · exact g32p_supplierForest_actual_120172
  · exact g32p_supplierForest_actual_120196
  · exact g32p_supplierForest_actual_120395
  · exact g32p_supplierForest_actual_120522
  · exact g32p_supplierForest_actual_120614
  · exact g32p_supplierForest_actual_120667
  · exact g32p_supplierForest_actual_120725
  · exact g32p_supplierForest_actual_120896
  · exact g32p_supplierForest_actual_120917
  · exact g32p_supplierForest_actual_120998
  · exact g32p_supplierForest_actual_121005
  · exact g32p_supplierForest_actual_121041
  · exact g32p_supplierForest_actual_121102
  · exact g32p_supplierForest_actual_121123
  · exact g32p_supplierForest_actual_121154
  · exact g32p_supplierForest_actual_121170
  · exact g32p_supplierForest_actual_121176
  · exact g32p_supplierForest_actual_121183
  · exact g32p_supplierForest_actual_121303
  · exact g32p_supplierForest_actual_121363
  · exact g32p_supplierForest_actual_121367
  · exact g32p_supplierForest_actual_121433
  · exact g32p_supplierForest_actual_121439
  · exact g32p_supplierForest_actual_121478
  · exact g32p_supplierForest_actual_121486
  · exact g32p_supplierForest_actual_121491
  · exact g32p_supplierForest_actual_121547
  · exact g32p_supplierForest_actual_121561
  · exact g32p_supplierForest_actual_121663
  · exact g32p_supplierForest_actual_121707
  · exact g32p_supplierForest_actual_121751

def g32p_supplierForest_nodes_140 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_121778 else g32p_supplierForest_node_121800) else (if i.val < 3 then g32p_supplierForest_node_121928 else g32p_supplierForest_node_121983)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_122082 else g32p_supplierForest_node_122144) else (if i.val < 7 then g32p_supplierForest_node_122165 else g32p_supplierForest_node_122191))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_122200 else g32p_supplierForest_node_122203) else (if i.val < 11 then g32p_supplierForest_node_122225 else g32p_supplierForest_node_122263)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_122306 else g32p_supplierForest_node_122328) else (if i.val < 15 then g32p_supplierForest_node_122602 else g32p_supplierForest_node_122603)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_122681 else g32p_supplierForest_node_122711) else (if i.val < 19 then g32p_supplierForest_node_122852 else g32p_supplierForest_node_122918)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_122932 else g32p_supplierForest_node_122985) else (if i.val < 23 then g32p_supplierForest_node_123007 else g32p_supplierForest_node_123035))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_123153 else g32p_supplierForest_node_123290) else (if i.val < 27 then g32p_supplierForest_node_123431 else g32p_supplierForest_node_123463)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_123464 else g32p_supplierForest_node_123486) else (if i.val < 31 then g32p_supplierForest_node_123529 else g32p_supplierForest_node_123577))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_123588 else g32p_supplierForest_node_123721) else (if i.val < 35 then g32p_supplierForest_node_123807 else g32p_supplierForest_node_123823)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_123896 else g32p_supplierForest_node_124005) else (if i.val < 39 then g32p_supplierForest_node_124016 else g32p_supplierForest_node_124018))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_124056 else g32p_supplierForest_node_124172) else (if i.val < 43 then g32p_supplierForest_node_124181 else g32p_supplierForest_node_124217)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_124252 else g32p_supplierForest_node_124447) else (if i.val < 47 then g32p_supplierForest_node_124455 else g32p_supplierForest_node_124601)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_124608 else g32p_supplierForest_node_124630) else (if i.val < 51 then g32p_supplierForest_node_124646 else g32p_supplierForest_node_124686)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_124771 else g32p_supplierForest_node_124783) else (if i.val < 55 then g32p_supplierForest_node_124972 else g32p_supplierForest_node_125046))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_125162 else g32p_supplierForest_node_125270) else (if i.val < 59 then g32p_supplierForest_node_125273 else g32p_supplierForest_node_125311)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_125364 else g32p_supplierForest_node_125367) else (if i.val < 63 then g32p_supplierForest_node_125398 else g32p_supplierForest_node_125430)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_125676 else g32p_supplierForest_node_125722) else (if i.val < 67 then g32p_supplierForest_node_125769 else g32p_supplierForest_node_125785)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_125817 else g32p_supplierForest_node_125830) else (if i.val < 71 then g32p_supplierForest_node_125857 else g32p_supplierForest_node_125911))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_126200 else g32p_supplierForest_node_126205) else (if i.val < 75 then g32p_supplierForest_node_126208 else g32p_supplierForest_node_126352)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_126380 else g32p_supplierForest_node_126381) else (if i.val < 79 then g32p_supplierForest_node_126402 else g32p_supplierForest_node_126503)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_126519 else g32p_supplierForest_node_126558) else (if i.val < 83 then g32p_supplierForest_node_126608 else g32p_supplierForest_node_126659)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_126665 else g32p_supplierForest_node_126705) else (if i.val < 87 then g32p_supplierForest_node_126903 else g32p_supplierForest_node_126994))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_127001 else g32p_supplierForest_node_127013) else (if i.val < 91 then g32p_supplierForest_node_127085 else g32p_supplierForest_node_127226)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_127330 else g32p_supplierForest_node_127526) else (if i.val < 95 then g32p_supplierForest_node_127574 else g32p_supplierForest_node_127706))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_127718 else g32p_supplierForest_node_127739) else (if i.val < 99 then g32p_supplierForest_node_127756 else g32p_supplierForest_node_128002)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_128107 else g32p_supplierForest_node_128129) else (if i.val < 103 then g32p_supplierForest_node_128151 else g32p_supplierForest_node_128190))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_128220 else g32p_supplierForest_node_128286) else (if i.val < 107 then g32p_supplierForest_node_128417 else g32p_supplierForest_node_128444)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_128482 else g32p_supplierForest_node_128674) else (if i.val < 111 then g32p_supplierForest_node_128851 else g32p_supplierForest_node_128852)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_128870 else g32p_supplierForest_node_128904) else (if i.val < 115 then g32p_supplierForest_node_128941 else g32p_supplierForest_node_128962)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_128965 else g32p_supplierForest_node_128996) else (if i.val < 119 then g32p_supplierForest_node_129323 else g32p_supplierForest_node_129328))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_129362 else g32p_supplierForest_node_129546) else (if i.val < 123 then g32p_supplierForest_node_129599 else g32p_supplierForest_node_129708)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_129734 else g32p_supplierForest_node_129757) else (if i.val < 127 then g32p_supplierForest_node_129920 else g32p_supplierForest_node_130042))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_130114 else g32p_supplierForest_node_130186) else (if i.val < 131 then g32p_supplierForest_node_130295 else g32p_supplierForest_node_130297)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_130318 else g32p_supplierForest_node_130381) else (if i.val < 135 then g32p_supplierForest_node_130469 else g32p_supplierForest_node_130545))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_130626 else g32p_supplierForest_node_130673) else (if i.val < 139 then g32p_supplierForest_node_130699 else g32p_supplierForest_node_130712)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_130792 else g32p_supplierForest_node_130835) else (if i.val < 143 then g32p_supplierForest_node_130863 else g32p_supplierForest_node_130899)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_131083 else g32p_supplierForest_node_131240) else (if i.val < 147 then g32p_supplierForest_node_131245 else g32p_supplierForest_node_131368)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_131539 else g32p_supplierForest_node_131644) else (if i.val < 151 then g32p_supplierForest_node_131750 else g32p_supplierForest_node_131813))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_131836 else g32p_supplierForest_node_131893) else (if i.val < 155 then g32p_supplierForest_node_131974 else g32p_supplierForest_node_132142)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_132179 else g32p_supplierForest_node_132186) else (if i.val < 159 then g32p_supplierForest_node_132211 else g32p_supplierForest_node_132402))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_132480 else g32p_supplierForest_node_132537) else (if i.val < 163 then g32p_supplierForest_node_132548 else g32p_supplierForest_node_132680)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_132718 else g32p_supplierForest_node_132783) else (if i.val < 167 then g32p_supplierForest_node_132790 else g32p_supplierForest_node_132796))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_133015 else g32p_supplierForest_node_133045) else (if i.val < 171 then g32p_supplierForest_node_133067 else g32p_supplierForest_node_133089)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_133101 else g32p_supplierForest_node_133168) else (if i.val < 175 then g32p_supplierForest_node_133231 else g32p_supplierForest_node_133379)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_133449 else g32p_supplierForest_node_133476) else (if i.val < 179 then g32p_supplierForest_node_133489 else g32p_supplierForest_node_133514)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_133585 else g32p_supplierForest_node_133593) else (if i.val < 183 then g32p_supplierForest_node_133715 else g32p_supplierForest_node_133821))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_133860 else g32p_supplierForest_node_133937) else (if i.val < 187 then g32p_supplierForest_node_133953 else g32p_supplierForest_node_133996)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_134025 else g32p_supplierForest_node_134096) else (if i.val < 191 then g32p_supplierForest_node_134100 else g32p_supplierForest_node_134107)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_134114 else g32p_supplierForest_node_134158) else (if i.val < 195 then g32p_supplierForest_node_134166 else g32p_supplierForest_node_134182)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_134283 else g32p_supplierForest_node_134351) else (if i.val < 199 then g32p_supplierForest_node_134360 else g32p_supplierForest_node_134375))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_134376 else g32p_supplierForest_node_134390) else (if i.val < 203 then g32p_supplierForest_node_134581 else g32p_supplierForest_node_134624)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_134637 else g32p_supplierForest_node_134661) else (if i.val < 207 then g32p_supplierForest_node_134700 else g32p_supplierForest_node_134709)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_134778 else g32p_supplierForest_node_134819) else (if i.val < 211 then g32p_supplierForest_node_134937 else g32p_supplierForest_node_135117)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_135163 else g32p_supplierForest_node_135193) else (if i.val < 215 then g32p_supplierForest_node_135226 else g32p_supplierForest_node_135319))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_135379 else g32p_supplierForest_node_135384) else (if i.val < 219 then g32p_supplierForest_node_135413 else g32p_supplierForest_node_135436)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_135478 else g32p_supplierForest_node_135621) else (if i.val < 223 then g32p_supplierForest_node_135661 else g32p_supplierForest_node_135686))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_135711 else g32p_supplierForest_node_135807) else (if i.val < 227 then g32p_supplierForest_node_135823 else g32p_supplierForest_node_135872)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_135888 else g32p_supplierForest_node_135894) else (if i.val < 231 then g32p_supplierForest_node_135907 else g32p_supplierForest_node_135985))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_136016 else g32p_supplierForest_node_136367) else (if i.val < 235 then g32p_supplierForest_node_136369 else g32p_supplierForest_node_136387)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_136470 else g32p_supplierForest_node_136506) else (if i.val < 239 then g32p_supplierForest_node_136557 else g32p_supplierForest_node_136604)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_136669 else g32p_supplierForest_node_136698) else (if i.val < 243 then g32p_supplierForest_node_136770 else g32p_supplierForest_node_136931)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_136956 else g32p_supplierForest_node_136993) else (if i.val < 247 then g32p_supplierForest_node_137014 else g32p_supplierForest_node_137062))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_137130 else g32p_supplierForest_node_137250) else (if i.val < 251 then g32p_supplierForest_node_137394 else g32p_supplierForest_node_137474)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_137498 else g32p_supplierForest_node_137520) else (if i.val < 255 then g32p_supplierForest_node_137574 else g32p_supplierForest_node_137637))))))))

def g32p_supplierForest_classes_140 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 57 else 62) else (if i.val < 3 then 30 else 57)) else (if i.val < 6 then (if i.val < 5 then 57 else 60) else (if i.val < 7 then 30 else 60))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 30 else 60) else (if i.val < 11 then 60 else 57)) else (if i.val < 14 then (if i.val < 13 then 15 else 29) else (if i.val < 15 then 16 else 57)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 30 else 57) else (if i.val < 19 then 60 else 59)) else (if i.val < 22 then (if i.val < 21 then 60 else 63) else (if i.val < 23 then 57 else 60))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 60 else 36) else (if i.val < 27 then 16 else 60)) else (if i.val < 30 then (if i.val < 29 then 36 else 57) else (if i.val < 31 then 60 else 62))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 59 else 63) else (if i.val < 35 then 60 else 58)) else (if i.val < 38 then (if i.val < 37 then 61 else 62) else (if i.val < 39 then 57 else 90))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 57 else 60) else (if i.val < 43 then 57 else 60)) else (if i.val < 46 then (if i.val < 45 then 62 else 57) else (if i.val < 47 then 57 else 60)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 29 else 30) else (if i.val < 51 then 30 else 62)) else (if i.val < 54 then (if i.val < 53 then 60 else 33) else (if i.val < 55 then 60 else 57))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 30 else 57) else (if i.val < 59 then 66 else 57)) else (if i.val < 62 then (if i.val < 61 then 60 else 57) else (if i.val < 63 then 29 else 30)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 57 else 57) else (if i.val < 67 then 57 else 57)) else (if i.val < 70 then (if i.val < 69 then 60 else 60) else (if i.val < 71 then 57 else 30))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 60 else 57) else (if i.val < 75 then 57 else 57)) else (if i.val < 78 then (if i.val < 77 then 60 else 57) else (if i.val < 79 then 30 else 57)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 29 else 30) else (if i.val < 83 then 30 else 57)) else (if i.val < 86 then (if i.val < 85 then 62 else 30) else (if i.val < 87 then 59 else 60))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 60 else 60) else (if i.val < 91 then 61 else 60)) else (if i.val < 94 then (if i.val < 93 then 60 else 57) else (if i.val < 95 then 60 else 29))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 57 else 29) else (if i.val < 99 then 30 else 73)) else (if i.val < 102 then (if i.val < 101 then 21 else 68) else (if i.val < 103 then 42 else 38))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 68 else 21) else (if i.val < 107 then 38 else 68)) else (if i.val < 110 then (if i.val < 109 then 40 else 38) else (if i.val < 111 then 38 else 20)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 38 else 71) else (if i.val < 115 then 71 else 21)) else (if i.val < 118 then (if i.val < 117 then 38 else 38) else (if i.val < 119 then 73 else 38))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 21 else 38) else (if i.val < 123 then 38 else 70)) else (if i.val < 126 then (if i.val < 125 then 38 else 21) else (if i.val < 127 then 21 else 71))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 38 else 21) else (if i.val < 131 then 38 else 38)) else (if i.val < 134 then (if i.val < 133 then 38 else 70) else (if i.val < 135 then 38 else 68))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 38 else 74) else (if i.val < 139 then 21 else 21)) else (if i.val < 142 then (if i.val < 141 then 38 else 72) else (if i.val < 143 then 38 else 21)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 38 else 71) else (if i.val < 147 then 71 else 38)) else (if i.val < 150 then (if i.val < 149 then 68 else 73) else (if i.val < 151 then 73 else 72))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 38 else 38) else (if i.val < 155 then 38 else 21)) else (if i.val < 158 then (if i.val < 157 then 38 else 38) else (if i.val < 159 then 38 else 38))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 38 else 38) else (if i.val < 163 then 22 else 38)) else (if i.val < 166 then (if i.val < 165 then 38 else 73) else (if i.val < 167 then 73 else 38))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 21 else 38) else (if i.val < 171 then 38 else 71)) else (if i.val < 174 then (if i.val < 173 then 38 else 21) else (if i.val < 175 then 21 else 75)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 21 else 73) else (if i.val < 179 then 68 else 73)) else (if i.val < 182 then (if i.val < 181 then 73 else 38) else (if i.val < 183 then 38 else 38))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 71 else 38) else (if i.val < 187 then 38 else 38)) else (if i.val < 190 then (if i.val < 189 then 72 else 68) else (if i.val < 191 then 38 else 42)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 21 else 73) else (if i.val < 195 then 73 else 68)) else (if i.val < 198 then (if i.val < 197 then 42 else 73) else (if i.val < 199 then 21 else 21))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 38 else 42) else (if i.val < 203 then 38 else 74)) else (if i.val < 206 then (if i.val < 205 then 42 else 73) else (if i.val < 207 then 73 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 73 else 73) else (if i.val < 211 then 21 else 38)) else (if i.val < 214 then (if i.val < 213 then 38 else 38) else (if i.val < 215 then 38 else 70))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 38 else 38) else (if i.val < 219 then 73 else 38)) else (if i.val < 222 then (if i.val < 221 then 21 else 21) else (if i.val < 223 then 38 else 70))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 41 else 73) else (if i.val < 227 then 38 else 38)) else (if i.val < 230 then (if i.val < 229 then 73 else 73) else (if i.val < 231 then 94 else 73))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 38 else 73) else (if i.val < 235 then 73 else 73)) else (if i.val < 238 then (if i.val < 237 then 38 else 73) else (if i.val < 239 then 21 else 38)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 38 else 38) else (if i.val < 243 then 21 else 38)) else (if i.val < 246 then (if i.val < 245 then 38 else 38) else (if i.val < 247 then 21 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 38 else 38) else (if i.val < 251 then 68 else 38)) else (if i.val < 254 then (if i.val < 253 then 21 else 38) else (if i.val < 255 then 21 else 21))))))))

theorem g32p_supplierForest_actual_140 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_140 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_140 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_121778
  · exact g32p_supplierForest_actual_121800
  · exact g32p_supplierForest_actual_121928
  · exact g32p_supplierForest_actual_121983
  · exact g32p_supplierForest_actual_122082
  · exact g32p_supplierForest_actual_122144
  · exact g32p_supplierForest_actual_122165
  · exact g32p_supplierForest_actual_122191
  · exact g32p_supplierForest_actual_122200
  · exact g32p_supplierForest_actual_122203
  · exact g32p_supplierForest_actual_122225
  · exact g32p_supplierForest_actual_122263
  · exact g32p_supplierForest_actual_122306
  · exact g32p_supplierForest_actual_122328
  · exact g32p_supplierForest_actual_122602
  · exact g32p_supplierForest_actual_122603
  · exact g32p_supplierForest_actual_122681
  · exact g32p_supplierForest_actual_122711
  · exact g32p_supplierForest_actual_122852
  · exact g32p_supplierForest_actual_122918
  · exact g32p_supplierForest_actual_122932
  · exact g32p_supplierForest_actual_122985
  · exact g32p_supplierForest_actual_123007
  · exact g32p_supplierForest_actual_123035
  · exact g32p_supplierForest_actual_123153
  · exact g32p_supplierForest_actual_123290
  · exact g32p_supplierForest_actual_123431
  · exact g32p_supplierForest_actual_123463
  · exact g32p_supplierForest_actual_123464
  · exact g32p_supplierForest_actual_123486
  · exact g32p_supplierForest_actual_123529
  · exact g32p_supplierForest_actual_123577
  · exact g32p_supplierForest_actual_123588
  · exact g32p_supplierForest_actual_123721
  · exact g32p_supplierForest_actual_123807
  · exact g32p_supplierForest_actual_123823
  · exact g32p_supplierForest_actual_123896
  · exact g32p_supplierForest_actual_124005
  · exact g32p_supplierForest_actual_124016
  · exact g32p_supplierForest_actual_124018
  · exact g32p_supplierForest_actual_124056
  · exact g32p_supplierForest_actual_124172
  · exact g32p_supplierForest_actual_124181
  · exact g32p_supplierForest_actual_124217
  · exact g32p_supplierForest_actual_124252
  · exact g32p_supplierForest_actual_124447
  · exact g32p_supplierForest_actual_124455
  · exact g32p_supplierForest_actual_124601
  · exact g32p_supplierForest_actual_124608
  · exact g32p_supplierForest_actual_124630
  · exact g32p_supplierForest_actual_124646
  · exact g32p_supplierForest_actual_124686
  · exact g32p_supplierForest_actual_124771
  · exact g32p_supplierForest_actual_124783
  · exact g32p_supplierForest_actual_124972
  · exact g32p_supplierForest_actual_125046
  · exact g32p_supplierForest_actual_125162
  · exact g32p_supplierForest_actual_125270
  · exact g32p_supplierForest_actual_125273
  · exact g32p_supplierForest_actual_125311
  · exact g32p_supplierForest_actual_125364
  · exact g32p_supplierForest_actual_125367
  · exact g32p_supplierForest_actual_125398
  · exact g32p_supplierForest_actual_125430
  · exact g32p_supplierForest_actual_125676
  · exact g32p_supplierForest_actual_125722
  · exact g32p_supplierForest_actual_125769
  · exact g32p_supplierForest_actual_125785
  · exact g32p_supplierForest_actual_125817
  · exact g32p_supplierForest_actual_125830
  · exact g32p_supplierForest_actual_125857
  · exact g32p_supplierForest_actual_125911
  · exact g32p_supplierForest_actual_126200
  · exact g32p_supplierForest_actual_126205
  · exact g32p_supplierForest_actual_126208
  · exact g32p_supplierForest_actual_126352
  · exact g32p_supplierForest_actual_126380
  · exact g32p_supplierForest_actual_126381
  · exact g32p_supplierForest_actual_126402
  · exact g32p_supplierForest_actual_126503
  · exact g32p_supplierForest_actual_126519
  · exact g32p_supplierForest_actual_126558
  · exact g32p_supplierForest_actual_126608
  · exact g32p_supplierForest_actual_126659
  · exact g32p_supplierForest_actual_126665
  · exact g32p_supplierForest_actual_126705
  · exact g32p_supplierForest_actual_126903
  · exact g32p_supplierForest_actual_126994
  · exact g32p_supplierForest_actual_127001
  · exact g32p_supplierForest_actual_127013
  · exact g32p_supplierForest_actual_127085
  · exact g32p_supplierForest_actual_127226
  · exact g32p_supplierForest_actual_127330
  · exact g32p_supplierForest_actual_127526
  · exact g32p_supplierForest_actual_127574
  · exact g32p_supplierForest_actual_127706
  · exact g32p_supplierForest_actual_127718
  · exact g32p_supplierForest_actual_127739
  · exact g32p_supplierForest_actual_127756
  · exact g32p_supplierForest_actual_128002
  · exact g32p_supplierForest_actual_128107
  · exact g32p_supplierForest_actual_128129
  · exact g32p_supplierForest_actual_128151
  · exact g32p_supplierForest_actual_128190
  · exact g32p_supplierForest_actual_128220
  · exact g32p_supplierForest_actual_128286
  · exact g32p_supplierForest_actual_128417
  · exact g32p_supplierForest_actual_128444
  · exact g32p_supplierForest_actual_128482
  · exact g32p_supplierForest_actual_128674
  · exact g32p_supplierForest_actual_128851
  · exact g32p_supplierForest_actual_128852
  · exact g32p_supplierForest_actual_128870
  · exact g32p_supplierForest_actual_128904
  · exact g32p_supplierForest_actual_128941
  · exact g32p_supplierForest_actual_128962
  · exact g32p_supplierForest_actual_128965
  · exact g32p_supplierForest_actual_128996
  · exact g32p_supplierForest_actual_129323
  · exact g32p_supplierForest_actual_129328
  · exact g32p_supplierForest_actual_129362
  · exact g32p_supplierForest_actual_129546
  · exact g32p_supplierForest_actual_129599
  · exact g32p_supplierForest_actual_129708
  · exact g32p_supplierForest_actual_129734
  · exact g32p_supplierForest_actual_129757
  · exact g32p_supplierForest_actual_129920
  · exact g32p_supplierForest_actual_130042
  · exact g32p_supplierForest_actual_130114
  · exact g32p_supplierForest_actual_130186
  · exact g32p_supplierForest_actual_130295
  · exact g32p_supplierForest_actual_130297
  · exact g32p_supplierForest_actual_130318
  · exact g32p_supplierForest_actual_130381
  · exact g32p_supplierForest_actual_130469
  · exact g32p_supplierForest_actual_130545
  · exact g32p_supplierForest_actual_130626
  · exact g32p_supplierForest_actual_130673
  · exact g32p_supplierForest_actual_130699
  · exact g32p_supplierForest_actual_130712
  · exact g32p_supplierForest_actual_130792
  · exact g32p_supplierForest_actual_130835
  · exact g32p_supplierForest_actual_130863
  · exact g32p_supplierForest_actual_130899
  · exact g32p_supplierForest_actual_131083
  · exact g32p_supplierForest_actual_131240
  · exact g32p_supplierForest_actual_131245
  · exact g32p_supplierForest_actual_131368
  · exact g32p_supplierForest_actual_131539
  · exact g32p_supplierForest_actual_131644
  · exact g32p_supplierForest_actual_131750
  · exact g32p_supplierForest_actual_131813
  · exact g32p_supplierForest_actual_131836
  · exact g32p_supplierForest_actual_131893
  · exact g32p_supplierForest_actual_131974
  · exact g32p_supplierForest_actual_132142
  · exact g32p_supplierForest_actual_132179
  · exact g32p_supplierForest_actual_132186
  · exact g32p_supplierForest_actual_132211
  · exact g32p_supplierForest_actual_132402
  · exact g32p_supplierForest_actual_132480
  · exact g32p_supplierForest_actual_132537
  · exact g32p_supplierForest_actual_132548
  · exact g32p_supplierForest_actual_132680
  · exact g32p_supplierForest_actual_132718
  · exact g32p_supplierForest_actual_132783
  · exact g32p_supplierForest_actual_132790
  · exact g32p_supplierForest_actual_132796
  · exact g32p_supplierForest_actual_133015
  · exact g32p_supplierForest_actual_133045
  · exact g32p_supplierForest_actual_133067
  · exact g32p_supplierForest_actual_133089
  · exact g32p_supplierForest_actual_133101
  · exact g32p_supplierForest_actual_133168
  · exact g32p_supplierForest_actual_133231
  · exact g32p_supplierForest_actual_133379
  · exact g32p_supplierForest_actual_133449
  · exact g32p_supplierForest_actual_133476
  · exact g32p_supplierForest_actual_133489
  · exact g32p_supplierForest_actual_133514
  · exact g32p_supplierForest_actual_133585
  · exact g32p_supplierForest_actual_133593
  · exact g32p_supplierForest_actual_133715
  · exact g32p_supplierForest_actual_133821
  · exact g32p_supplierForest_actual_133860
  · exact g32p_supplierForest_actual_133937
  · exact g32p_supplierForest_actual_133953
  · exact g32p_supplierForest_actual_133996
  · exact g32p_supplierForest_actual_134025
  · exact g32p_supplierForest_actual_134096
  · exact g32p_supplierForest_actual_134100
  · exact g32p_supplierForest_actual_134107
  · exact g32p_supplierForest_actual_134114
  · exact g32p_supplierForest_actual_134158
  · exact g32p_supplierForest_actual_134166
  · exact g32p_supplierForest_actual_134182
  · exact g32p_supplierForest_actual_134283
  · exact g32p_supplierForest_actual_134351
  · exact g32p_supplierForest_actual_134360
  · exact g32p_supplierForest_actual_134375
  · exact g32p_supplierForest_actual_134376
  · exact g32p_supplierForest_actual_134390
  · exact g32p_supplierForest_actual_134581
  · exact g32p_supplierForest_actual_134624
  · exact g32p_supplierForest_actual_134637
  · exact g32p_supplierForest_actual_134661
  · exact g32p_supplierForest_actual_134700
  · exact g32p_supplierForest_actual_134709
  · exact g32p_supplierForest_actual_134778
  · exact g32p_supplierForest_actual_134819
  · exact g32p_supplierForest_actual_134937
  · exact g32p_supplierForest_actual_135117
  · exact g32p_supplierForest_actual_135163
  · exact g32p_supplierForest_actual_135193
  · exact g32p_supplierForest_actual_135226
  · exact g32p_supplierForest_actual_135319
  · exact g32p_supplierForest_actual_135379
  · exact g32p_supplierForest_actual_135384
  · exact g32p_supplierForest_actual_135413
  · exact g32p_supplierForest_actual_135436
  · exact g32p_supplierForest_actual_135478
  · exact g32p_supplierForest_actual_135621
  · exact g32p_supplierForest_actual_135661
  · exact g32p_supplierForest_actual_135686
  · exact g32p_supplierForest_actual_135711
  · exact g32p_supplierForest_actual_135807
  · exact g32p_supplierForest_actual_135823
  · exact g32p_supplierForest_actual_135872
  · exact g32p_supplierForest_actual_135888
  · exact g32p_supplierForest_actual_135894
  · exact g32p_supplierForest_actual_135907
  · exact g32p_supplierForest_actual_135985
  · exact g32p_supplierForest_actual_136016
  · exact g32p_supplierForest_actual_136367
  · exact g32p_supplierForest_actual_136369
  · exact g32p_supplierForest_actual_136387
  · exact g32p_supplierForest_actual_136470
  · exact g32p_supplierForest_actual_136506
  · exact g32p_supplierForest_actual_136557
  · exact g32p_supplierForest_actual_136604
  · exact g32p_supplierForest_actual_136669
  · exact g32p_supplierForest_actual_136698
  · exact g32p_supplierForest_actual_136770
  · exact g32p_supplierForest_actual_136931
  · exact g32p_supplierForest_actual_136956
  · exact g32p_supplierForest_actual_136993
  · exact g32p_supplierForest_actual_137014
  · exact g32p_supplierForest_actual_137062
  · exact g32p_supplierForest_actual_137130
  · exact g32p_supplierForest_actual_137250
  · exact g32p_supplierForest_actual_137394
  · exact g32p_supplierForest_actual_137474
  · exact g32p_supplierForest_actual_137498
  · exact g32p_supplierForest_actual_137520
  · exact g32p_supplierForest_actual_137574
  · exact g32p_supplierForest_actual_137637

def g32p_supplierForest_nodes_141 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_137644 else g32p_supplierForest_node_137680) else (if i.val < 3 then g32p_supplierForest_node_137698 else g32p_supplierForest_node_137742)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_137783 else g32p_supplierForest_node_137921) else (if i.val < 7 then g32p_supplierForest_node_138109 else g32p_supplierForest_node_138257))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_138264 else g32p_supplierForest_node_138521) else (if i.val < 11 then g32p_supplierForest_node_138578 else g32p_supplierForest_node_138611)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_138665 else g32p_supplierForest_node_138747) else (if i.val < 15 then g32p_supplierForest_node_138749 else g32p_supplierForest_node_138785)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_138906 else g32p_supplierForest_node_138981) else (if i.val < 19 then g32p_supplierForest_node_139141 else g32p_supplierForest_node_139194)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_139361 else g32p_supplierForest_node_139559) else (if i.val < 23 then g32p_supplierForest_node_139576 else g32p_supplierForest_node_139649))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_139712 else g32p_supplierForest_node_139729) else (if i.val < 27 then g32p_supplierForest_node_139757 else g32p_supplierForest_node_139763)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_139926 else g32p_supplierForest_node_140010) else (if i.val < 31 then g32p_supplierForest_node_140100 else g32p_supplierForest_node_140231))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_140272 else g32p_supplierForest_node_140300) else (if i.val < 35 then g32p_supplierForest_node_140445 else g32p_supplierForest_node_140448)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_140454 else g32p_supplierForest_node_140744) else (if i.val < 39 then g32p_supplierForest_node_140766 else g32p_supplierForest_node_140836))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_140896 else g32p_supplierForest_node_140994) else (if i.val < 43 then g32p_supplierForest_node_141019 else g32p_supplierForest_node_141082)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_141116 else g32p_supplierForest_node_141191) else (if i.val < 47 then g32p_supplierForest_node_141214 else g32p_supplierForest_node_141220)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_141434 else g32p_supplierForest_node_141499) else (if i.val < 51 then g32p_supplierForest_node_141510 else g32p_supplierForest_node_141553)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_141611 else g32p_supplierForest_node_141674) else (if i.val < 55 then g32p_supplierForest_node_141887 else g32p_supplierForest_node_141893))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_142080 else g32p_supplierForest_node_142195) else (if i.val < 59 then g32p_supplierForest_node_142201 else g32p_supplierForest_node_142236)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_142300 else g32p_supplierForest_node_142482) else (if i.val < 63 then g32p_supplierForest_node_142499 else g32p_supplierForest_node_142540)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_142541 else g32p_supplierForest_node_142601) else (if i.val < 67 then g32p_supplierForest_node_142649 else g32p_supplierForest_node_142774)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_142821 else g32p_supplierForest_node_142830) else (if i.val < 71 then g32p_supplierForest_node_142847 else g32p_supplierForest_node_142894))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_142950 else g32p_supplierForest_node_143000) else (if i.val < 75 then g32p_supplierForest_node_143020 else g32p_supplierForest_node_143031)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_143090 else g32p_supplierForest_node_143098) else (if i.val < 79 then g32p_supplierForest_node_143208 else g32p_supplierForest_node_143229)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_143326 else g32p_supplierForest_node_143346) else (if i.val < 83 then g32p_supplierForest_node_143352 else g32p_supplierForest_node_143494)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_143532 else g32p_supplierForest_node_143687) else (if i.val < 87 then g32p_supplierForest_node_143890 else g32p_supplierForest_node_143978))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_144033 else g32p_supplierForest_node_144221) else (if i.val < 91 then g32p_supplierForest_node_144349 else g32p_supplierForest_node_144412)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_144454 else g32p_supplierForest_node_144751) else (if i.val < 95 then g32p_supplierForest_node_144909 else g32p_supplierForest_node_144988))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_145030 else g32p_supplierForest_node_145293) else (if i.val < 99 then g32p_supplierForest_node_145381 else g32p_supplierForest_node_145488)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_145494 else g32p_supplierForest_node_145549) else (if i.val < 103 then g32p_supplierForest_node_145712 else g32p_supplierForest_node_145771))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_145808 else g32p_supplierForest_node_145823) else (if i.val < 107 then g32p_supplierForest_node_146049 else g32p_supplierForest_node_146137)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_146165 else g32p_supplierForest_node_146186) else (if i.val < 111 then g32p_supplierForest_node_146197 else g32p_supplierForest_node_146300)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_146322 else g32p_supplierForest_node_146384) else (if i.val < 115 then g32p_supplierForest_node_146550 else g32p_supplierForest_node_146555)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_146615 else g32p_supplierForest_node_146711) else (if i.val < 119 then g32p_supplierForest_node_146724 else g32p_supplierForest_node_146726))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_146783 else g32p_supplierForest_node_146795) else (if i.val < 123 then g32p_supplierForest_node_146854 else g32p_supplierForest_node_146872)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_146941 else g32p_supplierForest_node_146949) else (if i.val < 127 then g32p_supplierForest_node_147064 else g32p_supplierForest_node_147115))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_147524 else g32p_supplierForest_node_147543) else (if i.val < 131 then g32p_supplierForest_node_147550 else g32p_supplierForest_node_147826)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_147843 else g32p_supplierForest_node_147867) else (if i.val < 135 then g32p_supplierForest_node_147880 else g32p_supplierForest_node_148043))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_148155 else g32p_supplierForest_node_148188) else (if i.val < 139 then g32p_supplierForest_node_148294 else g32p_supplierForest_node_148342)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_148532 else g32p_supplierForest_node_148566) else (if i.val < 143 then g32p_supplierForest_node_148579 else g32p_supplierForest_node_148662)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_148720 else g32p_supplierForest_node_148827) else (if i.val < 147 then g32p_supplierForest_node_148955 else g32p_supplierForest_node_148968)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_148991 else g32p_supplierForest_node_149093) else (if i.val < 151 then g32p_supplierForest_node_149151 else g32p_supplierForest_node_149207))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_149254 else g32p_supplierForest_node_149294) else (if i.val < 155 then g32p_supplierForest_node_149336 else g32p_supplierForest_node_149337)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_149351 else g32p_supplierForest_node_149420) else (if i.val < 159 then g32p_supplierForest_node_149791 else g32p_supplierForest_node_149818))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_149896 else g32p_supplierForest_node_149910) else (if i.val < 163 then g32p_supplierForest_node_150015 else g32p_supplierForest_node_150071)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_150090 else g32p_supplierForest_node_150100) else (if i.val < 167 then g32p_supplierForest_node_150235 else g32p_supplierForest_node_150236))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_150326 else g32p_supplierForest_node_150348) else (if i.val < 171 then g32p_supplierForest_node_150408 else g32p_supplierForest_node_150541)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_150597 else g32p_supplierForest_node_150704) else (if i.val < 175 then g32p_supplierForest_node_150713 else g32p_supplierForest_node_150764)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_150867 else g32p_supplierForest_node_150915) else (if i.val < 179 then g32p_supplierForest_node_151153 else g32p_supplierForest_node_151275)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_151316 else g32p_supplierForest_node_151488) else (if i.val < 183 then g32p_supplierForest_node_151700 else g32p_supplierForest_node_151714))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_151817 else g32p_supplierForest_node_151846) else (if i.val < 187 then g32p_supplierForest_node_152142 else g32p_supplierForest_node_152309)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_152366 else g32p_supplierForest_node_152441) else (if i.val < 191 then g32p_supplierForest_node_152626 else g32p_supplierForest_node_152979)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_153095 else g32p_supplierForest_node_153210) else (if i.val < 195 then g32p_supplierForest_node_153506 else g32p_supplierForest_node_153564)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_153669 else g32p_supplierForest_node_153806) else (if i.val < 199 then g32p_supplierForest_node_154016 else g32p_supplierForest_node_154038))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_154045 else g32p_supplierForest_node_154249) else (if i.val < 203 then g32p_supplierForest_node_154454 else g32p_supplierForest_node_154458)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_154570 else g32p_supplierForest_node_154662) else (if i.val < 207 then g32p_supplierForest_node_155277 else g32p_supplierForest_node_155287)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_000259 else g32p_supplierForest_node_000424) else (if i.val < 211 then g32p_supplierForest_node_000504 else g32p_supplierForest_node_000673)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_000884 else g32p_supplierForest_node_001075) else (if i.val < 215 then g32p_supplierForest_node_001095 else g32p_supplierForest_node_001910))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_002601 else g32p_supplierForest_node_002898) else (if i.val < 219 then g32p_supplierForest_node_002926 else g32p_supplierForest_node_003336)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_003432 else g32p_supplierForest_node_003697) else (if i.val < 223 then g32p_supplierForest_node_003701 else g32p_supplierForest_node_003763))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_003837 else g32p_supplierForest_node_004041) else (if i.val < 227 then g32p_supplierForest_node_004111 else g32p_supplierForest_node_004143)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_004418 else g32p_supplierForest_node_004444) else (if i.val < 231 then g32p_supplierForest_node_005218 else g32p_supplierForest_node_005271))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_005351 else g32p_supplierForest_node_005405) else (if i.val < 235 then g32p_supplierForest_node_005518 else g32p_supplierForest_node_005820)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_005948 else g32p_supplierForest_node_006015) else (if i.val < 239 then g32p_supplierForest_node_006248 else g32p_supplierForest_node_006352)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_006548 else g32p_supplierForest_node_006570) else (if i.val < 243 then g32p_supplierForest_node_006783 else g32p_supplierForest_node_006966)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_007421 else g32p_supplierForest_node_007432) else (if i.val < 247 then g32p_supplierForest_node_007441 else g32p_supplierForest_node_007647))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_007912 else g32p_supplierForest_node_007916) else (if i.val < 251 then g32p_supplierForest_node_008279 else g32p_supplierForest_node_008292)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_008311 else g32p_supplierForest_node_008508) else (if i.val < 255 then g32p_supplierForest_node_008806 else g32p_supplierForest_node_008946))))))))

def g32p_supplierForest_classes_141 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 38 else 38) else (if i.val < 3 then 38 else 21)) else (if i.val < 6 then (if i.val < 5 then 21 else 68) else (if i.val < 7 then 21 else 21))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 38 else 21) else (if i.val < 11 then 38 else 38)) else (if i.val < 14 then (if i.val < 13 then 38 else 73) else (if i.val < 15 then 21 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 73 else 73) else (if i.val < 19 then 21 else 20)) else (if i.val < 22 then (if i.val < 21 then 73 else 72) else (if i.val < 23 then 38 else 73))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 38 else 21) else (if i.val < 27 then 73 else 38)) else (if i.val < 30 then (if i.val < 29 then 73 else 21) else (if i.val < 31 then 73 else 21))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 73 else 38) else (if i.val < 35 then 73 else 38)) else (if i.val < 38 then (if i.val < 37 then 21 else 21) else (if i.val < 39 then 38 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 38 else 21) else (if i.val < 43 then 38 else 73)) else (if i.val < 46 then (if i.val < 45 then 38 else 73) else (if i.val < 47 then 43 else 43)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 73 else 73) else (if i.val < 51 then 38 else 21)) else (if i.val < 54 then (if i.val < 53 then 21 else 21) else (if i.val < 55 then 68 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 38) else (if i.val < 59 then 21 else 20)) else (if i.val < 62 then (if i.val < 61 then 74 else 71) else (if i.val < 63 then 21 else 73)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 73 else 43) else (if i.val < 67 then 72 else 38)) else (if i.val < 70 then (if i.val < 69 then 21 else 73) else (if i.val < 71 then 71 else 73))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 75 else 38) else (if i.val < 75 then 38 else 73)) else (if i.val < 78 then (if i.val < 77 then 38 else 38) else (if i.val < 79 then 38 else 38)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 21 else 20) else (if i.val < 83 then 74 else 73)) else (if i.val < 86 then (if i.val < 85 then 38 else 20) else (if i.val < 87 then 72 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 43 else 71) else (if i.val < 91 then 73 else 71)) else (if i.val < 94 then (if i.val < 93 then 42 else 47) else (if i.val < 95 then 26 else 25))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 46 else 49) else (if i.val < 99 then 49 else 54)) else (if i.val < 102 then (if i.val < 101 then 53 else 49) else (if i.val < 103 then 49 else 54))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 25 else 46) else (if i.val < 107 then 86 else 47)) else (if i.val < 110 then (if i.val < 109 then 54 else 86) else (if i.val < 111 then 49 else 47)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 46 else 49) else (if i.val < 115 then 46 else 55)) else (if i.val < 118 then (if i.val < 117 then 49 else 80) else (if i.val < 119 then 47 else 49))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 47 else 46) else (if i.val < 123 then 46 else 46)) else (if i.val < 126 then (if i.val < 125 then 54 else 47) else (if i.val < 127 then 53 else 46))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 46 else 46) else (if i.val < 131 then 49 else 86)) else (if i.val < 134 then (if i.val < 133 then 49 else 86) else (if i.val < 135 then 54 else 46))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 46 else 49) else (if i.val < 139 then 46 else 49)) else (if i.val < 142 then (if i.val < 141 then 49 else 53) else (if i.val < 143 then 49 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 26 else 86) else (if i.val < 147 then 54 else 86)) else (if i.val < 150 then (if i.val < 149 then 86 else 46) else (if i.val < 151 then 49 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 80) else (if i.val < 155 then 26 else 47)) else (if i.val < 158 then (if i.val < 157 then 26 else 49) else (if i.val < 159 then 26 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 55 else 46) else (if i.val < 163 then 25 else 47)) else (if i.val < 166 then (if i.val < 165 then 55 else 53) else (if i.val < 167 then 50 else 49))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 25 else 49) else (if i.val < 171 then 54 else 49)) else (if i.val < 174 then (if i.val < 173 then 49 else 55) else (if i.val < 175 then 49 else 55)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 46 else 49) else (if i.val < 179 then 49 else 47)) else (if i.val < 182 then (if i.val < 181 then 49 else 49) else (if i.val < 183 then 47 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 50 else 26) else (if i.val < 187 then 26 else 26)) else (if i.val < 190 then (if i.val < 189 then 47 else 86) else (if i.val < 191 then 30 else 30)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 60) else (if i.val < 195 then 30 else 60)) else (if i.val < 198 then (if i.val < 197 then 57 else 61) else (if i.val < 199 then 62 else 66))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 60 else 30) else (if i.val < 203 then 63 else 61)) else (if i.val < 206 then (if i.val < 205 then 30 else 30) else (if i.val < 207 then 38 else 38)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 15 else 15) else (if i.val < 211 then 21 else 21)) else (if i.val < 214 then (if i.val < 213 then 21 else 21) else (if i.val < 215 then 12 else 10))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 16 else 30) else (if i.val < 219 then 15 else 30)) else (if i.val < 222 then (if i.val < 221 then 30 else 16) else (if i.val < 223 then 30 else 16))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 29 else 16) else (if i.val < 227 then 30 else 30)) else (if i.val < 230 then (if i.val < 229 then 16 else 16) else (if i.val < 231 then 16 else 29))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 30 else 16) else (if i.val < 235 then 16 else 21)) else (if i.val < 238 then (if i.val < 237 then 21 else 38) else (if i.val < 239 then 21 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 38 else 38) else (if i.val < 243 then 21 else 38)) else (if i.val < 246 then (if i.val < 245 then 22 else 38) else (if i.val < 247 then 21 else 22))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 22 else 38) else (if i.val < 251 then 38 else 38)) else (if i.val < 254 then (if i.val < 253 then 21 else 21) else (if i.val < 255 then 21 else 22))))))))

theorem g32p_supplierForest_actual_141 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_141 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_141 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_137644
  · exact g32p_supplierForest_actual_137680
  · exact g32p_supplierForest_actual_137698
  · exact g32p_supplierForest_actual_137742
  · exact g32p_supplierForest_actual_137783
  · exact g32p_supplierForest_actual_137921
  · exact g32p_supplierForest_actual_138109
  · exact g32p_supplierForest_actual_138257
  · exact g32p_supplierForest_actual_138264
  · exact g32p_supplierForest_actual_138521
  · exact g32p_supplierForest_actual_138578
  · exact g32p_supplierForest_actual_138611
  · exact g32p_supplierForest_actual_138665
  · exact g32p_supplierForest_actual_138747
  · exact g32p_supplierForest_actual_138749
  · exact g32p_supplierForest_actual_138785
  · exact g32p_supplierForest_actual_138906
  · exact g32p_supplierForest_actual_138981
  · exact g32p_supplierForest_actual_139141
  · exact g32p_supplierForest_actual_139194
  · exact g32p_supplierForest_actual_139361
  · exact g32p_supplierForest_actual_139559
  · exact g32p_supplierForest_actual_139576
  · exact g32p_supplierForest_actual_139649
  · exact g32p_supplierForest_actual_139712
  · exact g32p_supplierForest_actual_139729
  · exact g32p_supplierForest_actual_139757
  · exact g32p_supplierForest_actual_139763
  · exact g32p_supplierForest_actual_139926
  · exact g32p_supplierForest_actual_140010
  · exact g32p_supplierForest_actual_140100
  · exact g32p_supplierForest_actual_140231
  · exact g32p_supplierForest_actual_140272
  · exact g32p_supplierForest_actual_140300
  · exact g32p_supplierForest_actual_140445
  · exact g32p_supplierForest_actual_140448
  · exact g32p_supplierForest_actual_140454
  · exact g32p_supplierForest_actual_140744
  · exact g32p_supplierForest_actual_140766
  · exact g32p_supplierForest_actual_140836
  · exact g32p_supplierForest_actual_140896
  · exact g32p_supplierForest_actual_140994
  · exact g32p_supplierForest_actual_141019
  · exact g32p_supplierForest_actual_141082
  · exact g32p_supplierForest_actual_141116
  · exact g32p_supplierForest_actual_141191
  · exact g32p_supplierForest_actual_141214
  · exact g32p_supplierForest_actual_141220
  · exact g32p_supplierForest_actual_141434
  · exact g32p_supplierForest_actual_141499
  · exact g32p_supplierForest_actual_141510
  · exact g32p_supplierForest_actual_141553
  · exact g32p_supplierForest_actual_141611
  · exact g32p_supplierForest_actual_141674
  · exact g32p_supplierForest_actual_141887
  · exact g32p_supplierForest_actual_141893
  · exact g32p_supplierForest_actual_142080
  · exact g32p_supplierForest_actual_142195
  · exact g32p_supplierForest_actual_142201
  · exact g32p_supplierForest_actual_142236
  · exact g32p_supplierForest_actual_142300
  · exact g32p_supplierForest_actual_142482
  · exact g32p_supplierForest_actual_142499
  · exact g32p_supplierForest_actual_142540
  · exact g32p_supplierForest_actual_142541
  · exact g32p_supplierForest_actual_142601
  · exact g32p_supplierForest_actual_142649
  · exact g32p_supplierForest_actual_142774
  · exact g32p_supplierForest_actual_142821
  · exact g32p_supplierForest_actual_142830
  · exact g32p_supplierForest_actual_142847
  · exact g32p_supplierForest_actual_142894
  · exact g32p_supplierForest_actual_142950
  · exact g32p_supplierForest_actual_143000
  · exact g32p_supplierForest_actual_143020
  · exact g32p_supplierForest_actual_143031
  · exact g32p_supplierForest_actual_143090
  · exact g32p_supplierForest_actual_143098
  · exact g32p_supplierForest_actual_143208
  · exact g32p_supplierForest_actual_143229
  · exact g32p_supplierForest_actual_143326
  · exact g32p_supplierForest_actual_143346
  · exact g32p_supplierForest_actual_143352
  · exact g32p_supplierForest_actual_143494
  · exact g32p_supplierForest_actual_143532
  · exact g32p_supplierForest_actual_143687
  · exact g32p_supplierForest_actual_143890
  · exact g32p_supplierForest_actual_143978
  · exact g32p_supplierForest_actual_144033
  · exact g32p_supplierForest_actual_144221
  · exact g32p_supplierForest_actual_144349
  · exact g32p_supplierForest_actual_144412
  · exact g32p_supplierForest_actual_144454
  · exact g32p_supplierForest_actual_144751
  · exact g32p_supplierForest_actual_144909
  · exact g32p_supplierForest_actual_144988
  · exact g32p_supplierForest_actual_145030
  · exact g32p_supplierForest_actual_145293
  · exact g32p_supplierForest_actual_145381
  · exact g32p_supplierForest_actual_145488
  · exact g32p_supplierForest_actual_145494
  · exact g32p_supplierForest_actual_145549
  · exact g32p_supplierForest_actual_145712
  · exact g32p_supplierForest_actual_145771
  · exact g32p_supplierForest_actual_145808
  · exact g32p_supplierForest_actual_145823
  · exact g32p_supplierForest_actual_146049
  · exact g32p_supplierForest_actual_146137
  · exact g32p_supplierForest_actual_146165
  · exact g32p_supplierForest_actual_146186
  · exact g32p_supplierForest_actual_146197
  · exact g32p_supplierForest_actual_146300
  · exact g32p_supplierForest_actual_146322
  · exact g32p_supplierForest_actual_146384
  · exact g32p_supplierForest_actual_146550
  · exact g32p_supplierForest_actual_146555
  · exact g32p_supplierForest_actual_146615
  · exact g32p_supplierForest_actual_146711
  · exact g32p_supplierForest_actual_146724
  · exact g32p_supplierForest_actual_146726
  · exact g32p_supplierForest_actual_146783
  · exact g32p_supplierForest_actual_146795
  · exact g32p_supplierForest_actual_146854
  · exact g32p_supplierForest_actual_146872
  · exact g32p_supplierForest_actual_146941
  · exact g32p_supplierForest_actual_146949
  · exact g32p_supplierForest_actual_147064
  · exact g32p_supplierForest_actual_147115
  · exact g32p_supplierForest_actual_147524
  · exact g32p_supplierForest_actual_147543
  · exact g32p_supplierForest_actual_147550
  · exact g32p_supplierForest_actual_147826
  · exact g32p_supplierForest_actual_147843
  · exact g32p_supplierForest_actual_147867
  · exact g32p_supplierForest_actual_147880
  · exact g32p_supplierForest_actual_148043
  · exact g32p_supplierForest_actual_148155
  · exact g32p_supplierForest_actual_148188
  · exact g32p_supplierForest_actual_148294
  · exact g32p_supplierForest_actual_148342
  · exact g32p_supplierForest_actual_148532
  · exact g32p_supplierForest_actual_148566
  · exact g32p_supplierForest_actual_148579
  · exact g32p_supplierForest_actual_148662
  · exact g32p_supplierForest_actual_148720
  · exact g32p_supplierForest_actual_148827
  · exact g32p_supplierForest_actual_148955
  · exact g32p_supplierForest_actual_148968
  · exact g32p_supplierForest_actual_148991
  · exact g32p_supplierForest_actual_149093
  · exact g32p_supplierForest_actual_149151
  · exact g32p_supplierForest_actual_149207
  · exact g32p_supplierForest_actual_149254
  · exact g32p_supplierForest_actual_149294
  · exact g32p_supplierForest_actual_149336
  · exact g32p_supplierForest_actual_149337
  · exact g32p_supplierForest_actual_149351
  · exact g32p_supplierForest_actual_149420
  · exact g32p_supplierForest_actual_149791
  · exact g32p_supplierForest_actual_149818
  · exact g32p_supplierForest_actual_149896
  · exact g32p_supplierForest_actual_149910
  · exact g32p_supplierForest_actual_150015
  · exact g32p_supplierForest_actual_150071
  · exact g32p_supplierForest_actual_150090
  · exact g32p_supplierForest_actual_150100
  · exact g32p_supplierForest_actual_150235
  · exact g32p_supplierForest_actual_150236
  · exact g32p_supplierForest_actual_150326
  · exact g32p_supplierForest_actual_150348
  · exact g32p_supplierForest_actual_150408
  · exact g32p_supplierForest_actual_150541
  · exact g32p_supplierForest_actual_150597
  · exact g32p_supplierForest_actual_150704
  · exact g32p_supplierForest_actual_150713
  · exact g32p_supplierForest_actual_150764
  · exact g32p_supplierForest_actual_150867
  · exact g32p_supplierForest_actual_150915
  · exact g32p_supplierForest_actual_151153
  · exact g32p_supplierForest_actual_151275
  · exact g32p_supplierForest_actual_151316
  · exact g32p_supplierForest_actual_151488
  · exact g32p_supplierForest_actual_151700
  · exact g32p_supplierForest_actual_151714
  · exact g32p_supplierForest_actual_151817
  · exact g32p_supplierForest_actual_151846
  · exact g32p_supplierForest_actual_152142
  · exact g32p_supplierForest_actual_152309
  · exact g32p_supplierForest_actual_152366
  · exact g32p_supplierForest_actual_152441
  · exact g32p_supplierForest_actual_152626
  · exact g32p_supplierForest_actual_152979
  · exact g32p_supplierForest_actual_153095
  · exact g32p_supplierForest_actual_153210
  · exact g32p_supplierForest_actual_153506
  · exact g32p_supplierForest_actual_153564
  · exact g32p_supplierForest_actual_153669
  · exact g32p_supplierForest_actual_153806
  · exact g32p_supplierForest_actual_154016
  · exact g32p_supplierForest_actual_154038
  · exact g32p_supplierForest_actual_154045
  · exact g32p_supplierForest_actual_154249
  · exact g32p_supplierForest_actual_154454
  · exact g32p_supplierForest_actual_154458
  · exact g32p_supplierForest_actual_154570
  · exact g32p_supplierForest_actual_154662
  · exact g32p_supplierForest_actual_155277
  · exact g32p_supplierForest_actual_155287
  · exact g32p_supplierForest_actual_000259
  · exact g32p_supplierForest_actual_000424
  · exact g32p_supplierForest_actual_000504
  · exact g32p_supplierForest_actual_000673
  · exact g32p_supplierForest_actual_000884
  · exact g32p_supplierForest_actual_001075
  · exact g32p_supplierForest_actual_001095
  · exact g32p_supplierForest_actual_001910
  · exact g32p_supplierForest_actual_002601
  · exact g32p_supplierForest_actual_002898
  · exact g32p_supplierForest_actual_002926
  · exact g32p_supplierForest_actual_003336
  · exact g32p_supplierForest_actual_003432
  · exact g32p_supplierForest_actual_003697
  · exact g32p_supplierForest_actual_003701
  · exact g32p_supplierForest_actual_003763
  · exact g32p_supplierForest_actual_003837
  · exact g32p_supplierForest_actual_004041
  · exact g32p_supplierForest_actual_004111
  · exact g32p_supplierForest_actual_004143
  · exact g32p_supplierForest_actual_004418
  · exact g32p_supplierForest_actual_004444
  · exact g32p_supplierForest_actual_005218
  · exact g32p_supplierForest_actual_005271
  · exact g32p_supplierForest_actual_005351
  · exact g32p_supplierForest_actual_005405
  · exact g32p_supplierForest_actual_005518
  · exact g32p_supplierForest_actual_005820
  · exact g32p_supplierForest_actual_005948
  · exact g32p_supplierForest_actual_006015
  · exact g32p_supplierForest_actual_006248
  · exact g32p_supplierForest_actual_006352
  · exact g32p_supplierForest_actual_006548
  · exact g32p_supplierForest_actual_006570
  · exact g32p_supplierForest_actual_006783
  · exact g32p_supplierForest_actual_006966
  · exact g32p_supplierForest_actual_007421
  · exact g32p_supplierForest_actual_007432
  · exact g32p_supplierForest_actual_007441
  · exact g32p_supplierForest_actual_007647
  · exact g32p_supplierForest_actual_007912
  · exact g32p_supplierForest_actual_007916
  · exact g32p_supplierForest_actual_008279
  · exact g32p_supplierForest_actual_008292
  · exact g32p_supplierForest_actual_008311
  · exact g32p_supplierForest_actual_008508
  · exact g32p_supplierForest_actual_008806
  · exact g32p_supplierForest_actual_008946

def g32p_supplierForest_nodes_142 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_009056 else g32p_supplierForest_node_009176) else (if i.val < 3 then g32p_supplierForest_node_009439 else g32p_supplierForest_node_009515)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_009517 else g32p_supplierForest_node_009720) else (if i.val < 7 then g32p_supplierForest_node_009888 else g32p_supplierForest_node_010115))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_010344 else g32p_supplierForest_node_010370) else (if i.val < 11 then g32p_supplierForest_node_010406 else g32p_supplierForest_node_010466)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_010488 else g32p_supplierForest_node_010575) else (if i.val < 15 then g32p_supplierForest_node_010800 else g32p_supplierForest_node_011059)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_011199 else g32p_supplierForest_node_011293) else (if i.val < 19 then g32p_supplierForest_node_011512 else g32p_supplierForest_node_011697)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_011732 else g32p_supplierForest_node_011938) else (if i.val < 23 then g32p_supplierForest_node_011983 else g32p_supplierForest_node_012044))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_012057 else g32p_supplierForest_node_012233) else (if i.val < 27 then g32p_supplierForest_node_012407 else g32p_supplierForest_node_012442)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_012650 else g32p_supplierForest_node_013444) else (if i.val < 31 then g32p_supplierForest_node_013591 else g32p_supplierForest_node_013737))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_014080 else g32p_supplierForest_node_014681) else (if i.val < 35 then g32p_supplierForest_node_014811 else g32p_supplierForest_node_014974)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_014999 else g32p_supplierForest_node_015032) else (if i.val < 39 then g32p_supplierForest_node_015339 else g32p_supplierForest_node_015360))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_015619 else g32p_supplierForest_node_015627) else (if i.val < 43 then g32p_supplierForest_node_015640 else g32p_supplierForest_node_016159)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_016284 else g32p_supplierForest_node_016530) else (if i.val < 47 then g32p_supplierForest_node_016743 else g32p_supplierForest_node_016882)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_016916 else g32p_supplierForest_node_016917) else (if i.val < 51 then g32p_supplierForest_node_016981 else g32p_supplierForest_node_017033)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_017172 else g32p_supplierForest_node_017247) else (if i.val < 55 then g32p_supplierForest_node_017471 else g32p_supplierForest_node_017621))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_017688 else g32p_supplierForest_node_017728) else (if i.val < 59 then g32p_supplierForest_node_018427 else g32p_supplierForest_node_018453)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_018600 else g32p_supplierForest_node_018678) else (if i.val < 63 then g32p_supplierForest_node_019148 else g32p_supplierForest_node_019222)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_019282 else g32p_supplierForest_node_019354) else (if i.val < 67 then g32p_supplierForest_node_019364 else g32p_supplierForest_node_019391)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_019410 else g32p_supplierForest_node_019700) else (if i.val < 71 then g32p_supplierForest_node_019820 else g32p_supplierForest_node_019823))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_019958 else g32p_supplierForest_node_020322) else (if i.val < 75 then g32p_supplierForest_node_020756 else g32p_supplierForest_node_020848)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_020855 else g32p_supplierForest_node_020951) else (if i.val < 79 then g32p_supplierForest_node_020961 else g32p_supplierForest_node_021164)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_021678 else g32p_supplierForest_node_021826) else (if i.val < 83 then g32p_supplierForest_node_021900 else g32p_supplierForest_node_021911)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_022161 else g32p_supplierForest_node_022547) else (if i.val < 87 then g32p_supplierForest_node_022705 else g32p_supplierForest_node_022957))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_023124 else g32p_supplierForest_node_023405) else (if i.val < 91 then g32p_supplierForest_node_023454 else g32p_supplierForest_node_023463)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_023581 else g32p_supplierForest_node_023641) else (if i.val < 95 then g32p_supplierForest_node_023669 else g32p_supplierForest_node_023779))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_023991 else g32p_supplierForest_node_024043) else (if i.val < 99 then g32p_supplierForest_node_024323 else g32p_supplierForest_node_024401)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_024917 else g32p_supplierForest_node_024956) else (if i.val < 103 then g32p_supplierForest_node_025162 else g32p_supplierForest_node_025980))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_026283 else g32p_supplierForest_node_026373) else (if i.val < 107 then g32p_supplierForest_node_026575 else g32p_supplierForest_node_026787)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_026849 else g32p_supplierForest_node_026996) else (if i.val < 111 then g32p_supplierForest_node_027032 else g32p_supplierForest_node_027060)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_027190 else g32p_supplierForest_node_027465) else (if i.val < 115 then g32p_supplierForest_node_027869 else g32p_supplierForest_node_027948)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_028126 else g32p_supplierForest_node_028363) else (if i.val < 119 then g32p_supplierForest_node_028779 else g32p_supplierForest_node_028781))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_029097 else g32p_supplierForest_node_029119) else (if i.val < 123 then g32p_supplierForest_node_029133 else g32p_supplierForest_node_029190)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_029219 else g32p_supplierForest_node_029222) else (if i.val < 127 then g32p_supplierForest_node_029395 else g32p_supplierForest_node_029469))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_029713 else g32p_supplierForest_node_029744) else (if i.val < 131 then g32p_supplierForest_node_029763 else g32p_supplierForest_node_029822)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_029829 else g32p_supplierForest_node_029994) else (if i.val < 135 then g32p_supplierForest_node_030061 else g32p_supplierForest_node_030102))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_030125 else g32p_supplierForest_node_030471) else (if i.val < 139 then g32p_supplierForest_node_030961 else g32p_supplierForest_node_030986)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_031860 else g32p_supplierForest_node_031986) else (if i.val < 143 then g32p_supplierForest_node_032025 else g32p_supplierForest_node_032077)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_032221 else g32p_supplierForest_node_032298) else (if i.val < 147 then g32p_supplierForest_node_032360 else g32p_supplierForest_node_032400)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_032680 else g32p_supplierForest_node_032687) else (if i.val < 151 then g32p_supplierForest_node_032855 else g32p_supplierForest_node_032974))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_033042 else g32p_supplierForest_node_033297) else (if i.val < 155 then g32p_supplierForest_node_033299 else g32p_supplierForest_node_033316)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_033595 else g32p_supplierForest_node_033887) else (if i.val < 159 then g32p_supplierForest_node_033992 else g32p_supplierForest_node_034040))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_034207 else g32p_supplierForest_node_034420) else (if i.val < 163 then g32p_supplierForest_node_034522 else g32p_supplierForest_node_034642)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_034687 else g32p_supplierForest_node_034735) else (if i.val < 167 then g32p_supplierForest_node_034867 else g32p_supplierForest_node_034885))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_035265 else g32p_supplierForest_node_035804) else (if i.val < 171 then g32p_supplierForest_node_035883 else g32p_supplierForest_node_036238)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_036436 else g32p_supplierForest_node_036703) else (if i.val < 175 then g32p_supplierForest_node_036864 else g32p_supplierForest_node_037160)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_037168 else g32p_supplierForest_node_037177) else (if i.val < 179 then g32p_supplierForest_node_037236 else g32p_supplierForest_node_037320)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_037384 else g32p_supplierForest_node_037480) else (if i.val < 183 then g32p_supplierForest_node_037498 else g32p_supplierForest_node_037581))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_037614 else g32p_supplierForest_node_037727) else (if i.val < 187 then g32p_supplierForest_node_037733 else g32p_supplierForest_node_037768)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_037891 else g32p_supplierForest_node_038071) else (if i.val < 191 then g32p_supplierForest_node_038111 else g32p_supplierForest_node_038233)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_038260 else g32p_supplierForest_node_038361) else (if i.val < 195 then g32p_supplierForest_node_038686 else g32p_supplierForest_node_038695)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_039081 else g32p_supplierForest_node_039478) else (if i.val < 199 then g32p_supplierForest_node_039856 else g32p_supplierForest_node_039943))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_040066 else g32p_supplierForest_node_040766) else (if i.val < 203 then g32p_supplierForest_node_040805 else g32p_supplierForest_node_040818)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_040877 else g32p_supplierForest_node_041010) else (if i.val < 207 then g32p_supplierForest_node_041043 else g32p_supplierForest_node_041164)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_041674 else g32p_supplierForest_node_041746) else (if i.val < 211 then g32p_supplierForest_node_041931 else g32p_supplierForest_node_042282)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_042525 else g32p_supplierForest_node_042725) else (if i.val < 215 then g32p_supplierForest_node_042846 else g32p_supplierForest_node_043082))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_043137 else g32p_supplierForest_node_043144) else (if i.val < 219 then g32p_supplierForest_node_043154 else g32p_supplierForest_node_043239)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_043393 else g32p_supplierForest_node_043584) else (if i.val < 223 then g32p_supplierForest_node_043751 else g32p_supplierForest_node_043858))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_043988 else g32p_supplierForest_node_044482) else (if i.val < 227 then g32p_supplierForest_node_044818 else g32p_supplierForest_node_044830)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_044897 else g32p_supplierForest_node_045013) else (if i.val < 231 then g32p_supplierForest_node_045151 else g32p_supplierForest_node_045196))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_045696 else g32p_supplierForest_node_046103) else (if i.val < 235 then g32p_supplierForest_node_046314 else g32p_supplierForest_node_046388)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_046441 else g32p_supplierForest_node_046478) else (if i.val < 239 then g32p_supplierForest_node_046620 else g32p_supplierForest_node_046629)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_046864 else g32p_supplierForest_node_046911) else (if i.val < 243 then g32p_supplierForest_node_047012 else g32p_supplierForest_node_047410)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_047710 else g32p_supplierForest_node_047827) else (if i.val < 247 then g32p_supplierForest_node_048219 else g32p_supplierForest_node_048264))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_048680 else g32p_supplierForest_node_048785) else (if i.val < 251 then g32p_supplierForest_node_049092 else g32p_supplierForest_node_049321)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_049419 else g32p_supplierForest_node_049493) else (if i.val < 255 then g32p_supplierForest_node_049759 else g32p_supplierForest_node_050065))))))))

def g32p_supplierForest_classes_142 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 7 else 38) else (if i.val < 3 then 38 else 22)) else (if i.val < 6 then (if i.val < 5 then 38 else 38) else (if i.val < 7 then 22 else 22))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 21 else 38) else (if i.val < 11 then 40 else 7)) else (if i.val < 14 then (if i.val < 13 then 22 else 40) else (if i.val < 15 then 20 else 21)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 22 else 21) else (if i.val < 19 then 38 else 38)) else (if i.val < 22 then (if i.val < 21 then 21 else 21) else (if i.val < 23 then 38 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 22 else 22) else (if i.val < 27 then 26 else 26)) else (if i.val < 30 then (if i.val < 29 then 50 else 49) else (if i.val < 31 then 26 else 49))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 26 else 47) else (if i.val < 35 then 26 else 9)) else (if i.val < 38 then (if i.val < 37 then 49 else 49) else (if i.val < 39 then 49 else 49))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 10 else 47) else (if i.val < 43 then 26 else 49)) else (if i.val < 46 then (if i.val < 45 then 49 else 49) else (if i.val < 47 then 48 else 47)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 49 else 49) else (if i.val < 51 then 49 else 49)) else (if i.val < 54 then (if i.val < 53 then 49 else 49) else (if i.val < 55 then 49 else 49))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 49 else 49) else (if i.val < 59 then 26 else 26)) else (if i.val < 62 then (if i.val < 61 then 12 else 25) else (if i.val < 63 then 49 else 26)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 49 else 49) else (if i.val < 67 then 26 else 49)) else (if i.val < 70 then (if i.val < 69 then 49 else 9) else (if i.val < 71 then 49 else 49))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 49 else 46) else (if i.val < 75 then 47 else 49)) else (if i.val < 78 then (if i.val < 77 then 47 else 49) else (if i.val < 79 then 49 else 49)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 46 else 49) else (if i.val < 83 then 49 else 49)) else (if i.val < 86 then (if i.val < 85 then 47 else 49) else (if i.val < 87 then 25 else 47))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 49 else 26) else (if i.val < 91 then 49 else 49)) else (if i.val < 94 then (if i.val < 93 then 50 else 49) else (if i.val < 95 then 49 else 47))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 49 else 49) else (if i.val < 99 then 26 else 49)) else (if i.val < 102 then (if i.val < 101 then 36 else 16) else (if i.val < 103 then 16 else 57))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 57 else 30) else (if i.val < 107 then 57 else 57)) else (if i.val < 110 then (if i.val < 109 then 57 else 58) else (if i.val < 111 then 57 else 57)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 16 else 30) else (if i.val < 115 then 57 else 30)) else (if i.val < 118 then (if i.val < 117 then 57 else 30) else (if i.val < 119 then 57 else 16))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 16 else 57) else (if i.val < 123 then 16 else 63)) else (if i.val < 126 then (if i.val < 125 then 57 else 30) else (if i.val < 127 then 14 else 16))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 30 else 57) else (if i.val < 131 then 16 else 30)) else (if i.val < 134 then (if i.val < 133 then 57 else 57) else (if i.val < 135 then 57 else 62))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 57 else 30) else (if i.val < 139 then 57 else 30)) else (if i.val < 142 then (if i.val < 141 then 57 else 16) else (if i.val < 143 then 16 else 14)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 57 else 57) else (if i.val < 147 then 57 else 60)) else (if i.val < 150 then (if i.val < 149 then 30 else 16) else (if i.val < 151 then 57 else 57))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 57 else 57) else (if i.val < 155 then 57 else 30)) else (if i.val < 158 then (if i.val < 157 then 16 else 57) else (if i.val < 159 then 16 else 30))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 30 else 57) else (if i.val < 163 then 57 else 57)) else (if i.val < 166 then (if i.val < 165 then 60 else 60) else (if i.val < 167 then 62 else 57))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 29 else 66) else (if i.val < 171 then 30 else 30)) else (if i.val < 174 then (if i.val < 173 then 63 else 60) else (if i.val < 175 then 57 else 57)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 30 else 57) else (if i.val < 179 then 30 else 30)) else (if i.val < 182 then (if i.val < 181 then 16 else 30) else (if i.val < 183 then 57 else 30))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 57 else 57) else (if i.val < 187 then 60 else 57)) else (if i.val < 190 then (if i.val < 189 then 57 else 57) else (if i.val < 191 then 30 else 57)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 30 else 57) else (if i.val < 195 then 57 else 57)) else (if i.val < 198 then (if i.val < 197 then 57 else 30) else (if i.val < 199 then 57 else 63))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 30 else 57) else (if i.val < 203 then 30 else 57)) else (if i.val < 206 then (if i.val < 205 then 57 else 30) else (if i.val < 207 then 57 else 33)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 57 else 30) else (if i.val < 211 then 30 else 57)) else (if i.val < 214 then (if i.val < 213 then 57 else 57) else (if i.val < 215 then 57 else 57))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 57 else 30) else (if i.val < 219 then 16 else 57)) else (if i.val < 222 then (if i.val < 221 then 57 else 57) else (if i.val < 223 then 16 else 57))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 60 else 38) else (if i.val < 227 then 38 else 38)) else (if i.val < 230 then (if i.val < 229 then 21 else 43) else (if i.val < 231 then 22 else 38))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 22 else 41) else (if i.val < 235 then 38 else 38)) else (if i.val < 238 then (if i.val < 237 then 38 else 21) else (if i.val < 239 then 38 else 21)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 22 else 38) else (if i.val < 243 then 21 else 38)) else (if i.val < 246 then (if i.val < 245 then 40 else 38) else (if i.val < 247 then 21 else 38))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 21 else 22) else (if i.val < 251 then 38 else 38)) else (if i.val < 254 then (if i.val < 253 then 39 else 38) else (if i.val < 255 then 38 else 38))))))))

theorem g32p_supplierForest_actual_142 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_142 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_142 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_009056
  · exact g32p_supplierForest_actual_009176
  · exact g32p_supplierForest_actual_009439
  · exact g32p_supplierForest_actual_009515
  · exact g32p_supplierForest_actual_009517
  · exact g32p_supplierForest_actual_009720
  · exact g32p_supplierForest_actual_009888
  · exact g32p_supplierForest_actual_010115
  · exact g32p_supplierForest_actual_010344
  · exact g32p_supplierForest_actual_010370
  · exact g32p_supplierForest_actual_010406
  · exact g32p_supplierForest_actual_010466
  · exact g32p_supplierForest_actual_010488
  · exact g32p_supplierForest_actual_010575
  · exact g32p_supplierForest_actual_010800
  · exact g32p_supplierForest_actual_011059
  · exact g32p_supplierForest_actual_011199
  · exact g32p_supplierForest_actual_011293
  · exact g32p_supplierForest_actual_011512
  · exact g32p_supplierForest_actual_011697
  · exact g32p_supplierForest_actual_011732
  · exact g32p_supplierForest_actual_011938
  · exact g32p_supplierForest_actual_011983
  · exact g32p_supplierForest_actual_012044
  · exact g32p_supplierForest_actual_012057
  · exact g32p_supplierForest_actual_012233
  · exact g32p_supplierForest_actual_012407
  · exact g32p_supplierForest_actual_012442
  · exact g32p_supplierForest_actual_012650
  · exact g32p_supplierForest_actual_013444
  · exact g32p_supplierForest_actual_013591
  · exact g32p_supplierForest_actual_013737
  · exact g32p_supplierForest_actual_014080
  · exact g32p_supplierForest_actual_014681
  · exact g32p_supplierForest_actual_014811
  · exact g32p_supplierForest_actual_014974
  · exact g32p_supplierForest_actual_014999
  · exact g32p_supplierForest_actual_015032
  · exact g32p_supplierForest_actual_015339
  · exact g32p_supplierForest_actual_015360
  · exact g32p_supplierForest_actual_015619
  · exact g32p_supplierForest_actual_015627
  · exact g32p_supplierForest_actual_015640
  · exact g32p_supplierForest_actual_016159
  · exact g32p_supplierForest_actual_016284
  · exact g32p_supplierForest_actual_016530
  · exact g32p_supplierForest_actual_016743
  · exact g32p_supplierForest_actual_016882
  · exact g32p_supplierForest_actual_016916
  · exact g32p_supplierForest_actual_016917
  · exact g32p_supplierForest_actual_016981
  · exact g32p_supplierForest_actual_017033
  · exact g32p_supplierForest_actual_017172
  · exact g32p_supplierForest_actual_017247
  · exact g32p_supplierForest_actual_017471
  · exact g32p_supplierForest_actual_017621
  · exact g32p_supplierForest_actual_017688
  · exact g32p_supplierForest_actual_017728
  · exact g32p_supplierForest_actual_018427
  · exact g32p_supplierForest_actual_018453
  · exact g32p_supplierForest_actual_018600
  · exact g32p_supplierForest_actual_018678
  · exact g32p_supplierForest_actual_019148
  · exact g32p_supplierForest_actual_019222
  · exact g32p_supplierForest_actual_019282
  · exact g32p_supplierForest_actual_019354
  · exact g32p_supplierForest_actual_019364
  · exact g32p_supplierForest_actual_019391
  · exact g32p_supplierForest_actual_019410
  · exact g32p_supplierForest_actual_019700
  · exact g32p_supplierForest_actual_019820
  · exact g32p_supplierForest_actual_019823
  · exact g32p_supplierForest_actual_019958
  · exact g32p_supplierForest_actual_020322
  · exact g32p_supplierForest_actual_020756
  · exact g32p_supplierForest_actual_020848
  · exact g32p_supplierForest_actual_020855
  · exact g32p_supplierForest_actual_020951
  · exact g32p_supplierForest_actual_020961
  · exact g32p_supplierForest_actual_021164
  · exact g32p_supplierForest_actual_021678
  · exact g32p_supplierForest_actual_021826
  · exact g32p_supplierForest_actual_021900
  · exact g32p_supplierForest_actual_021911
  · exact g32p_supplierForest_actual_022161
  · exact g32p_supplierForest_actual_022547
  · exact g32p_supplierForest_actual_022705
  · exact g32p_supplierForest_actual_022957
  · exact g32p_supplierForest_actual_023124
  · exact g32p_supplierForest_actual_023405
  · exact g32p_supplierForest_actual_023454
  · exact g32p_supplierForest_actual_023463
  · exact g32p_supplierForest_actual_023581
  · exact g32p_supplierForest_actual_023641
  · exact g32p_supplierForest_actual_023669
  · exact g32p_supplierForest_actual_023779
  · exact g32p_supplierForest_actual_023991
  · exact g32p_supplierForest_actual_024043
  · exact g32p_supplierForest_actual_024323
  · exact g32p_supplierForest_actual_024401
  · exact g32p_supplierForest_actual_024917
  · exact g32p_supplierForest_actual_024956
  · exact g32p_supplierForest_actual_025162
  · exact g32p_supplierForest_actual_025980
  · exact g32p_supplierForest_actual_026283
  · exact g32p_supplierForest_actual_026373
  · exact g32p_supplierForest_actual_026575
  · exact g32p_supplierForest_actual_026787
  · exact g32p_supplierForest_actual_026849
  · exact g32p_supplierForest_actual_026996
  · exact g32p_supplierForest_actual_027032
  · exact g32p_supplierForest_actual_027060
  · exact g32p_supplierForest_actual_027190
  · exact g32p_supplierForest_actual_027465
  · exact g32p_supplierForest_actual_027869
  · exact g32p_supplierForest_actual_027948
  · exact g32p_supplierForest_actual_028126
  · exact g32p_supplierForest_actual_028363
  · exact g32p_supplierForest_actual_028779
  · exact g32p_supplierForest_actual_028781
  · exact g32p_supplierForest_actual_029097
  · exact g32p_supplierForest_actual_029119
  · exact g32p_supplierForest_actual_029133
  · exact g32p_supplierForest_actual_029190
  · exact g32p_supplierForest_actual_029219
  · exact g32p_supplierForest_actual_029222
  · exact g32p_supplierForest_actual_029395
  · exact g32p_supplierForest_actual_029469
  · exact g32p_supplierForest_actual_029713
  · exact g32p_supplierForest_actual_029744
  · exact g32p_supplierForest_actual_029763
  · exact g32p_supplierForest_actual_029822
  · exact g32p_supplierForest_actual_029829
  · exact g32p_supplierForest_actual_029994
  · exact g32p_supplierForest_actual_030061
  · exact g32p_supplierForest_actual_030102
  · exact g32p_supplierForest_actual_030125
  · exact g32p_supplierForest_actual_030471
  · exact g32p_supplierForest_actual_030961
  · exact g32p_supplierForest_actual_030986
  · exact g32p_supplierForest_actual_031860
  · exact g32p_supplierForest_actual_031986
  · exact g32p_supplierForest_actual_032025
  · exact g32p_supplierForest_actual_032077
  · exact g32p_supplierForest_actual_032221
  · exact g32p_supplierForest_actual_032298
  · exact g32p_supplierForest_actual_032360
  · exact g32p_supplierForest_actual_032400
  · exact g32p_supplierForest_actual_032680
  · exact g32p_supplierForest_actual_032687
  · exact g32p_supplierForest_actual_032855
  · exact g32p_supplierForest_actual_032974
  · exact g32p_supplierForest_actual_033042
  · exact g32p_supplierForest_actual_033297
  · exact g32p_supplierForest_actual_033299
  · exact g32p_supplierForest_actual_033316
  · exact g32p_supplierForest_actual_033595
  · exact g32p_supplierForest_actual_033887
  · exact g32p_supplierForest_actual_033992
  · exact g32p_supplierForest_actual_034040
  · exact g32p_supplierForest_actual_034207
  · exact g32p_supplierForest_actual_034420
  · exact g32p_supplierForest_actual_034522
  · exact g32p_supplierForest_actual_034642
  · exact g32p_supplierForest_actual_034687
  · exact g32p_supplierForest_actual_034735
  · exact g32p_supplierForest_actual_034867
  · exact g32p_supplierForest_actual_034885
  · exact g32p_supplierForest_actual_035265
  · exact g32p_supplierForest_actual_035804
  · exact g32p_supplierForest_actual_035883
  · exact g32p_supplierForest_actual_036238
  · exact g32p_supplierForest_actual_036436
  · exact g32p_supplierForest_actual_036703
  · exact g32p_supplierForest_actual_036864
  · exact g32p_supplierForest_actual_037160
  · exact g32p_supplierForest_actual_037168
  · exact g32p_supplierForest_actual_037177
  · exact g32p_supplierForest_actual_037236
  · exact g32p_supplierForest_actual_037320
  · exact g32p_supplierForest_actual_037384
  · exact g32p_supplierForest_actual_037480
  · exact g32p_supplierForest_actual_037498
  · exact g32p_supplierForest_actual_037581
  · exact g32p_supplierForest_actual_037614
  · exact g32p_supplierForest_actual_037727
  · exact g32p_supplierForest_actual_037733
  · exact g32p_supplierForest_actual_037768
  · exact g32p_supplierForest_actual_037891
  · exact g32p_supplierForest_actual_038071
  · exact g32p_supplierForest_actual_038111
  · exact g32p_supplierForest_actual_038233
  · exact g32p_supplierForest_actual_038260
  · exact g32p_supplierForest_actual_038361
  · exact g32p_supplierForest_actual_038686
  · exact g32p_supplierForest_actual_038695
  · exact g32p_supplierForest_actual_039081
  · exact g32p_supplierForest_actual_039478
  · exact g32p_supplierForest_actual_039856
  · exact g32p_supplierForest_actual_039943
  · exact g32p_supplierForest_actual_040066
  · exact g32p_supplierForest_actual_040766
  · exact g32p_supplierForest_actual_040805
  · exact g32p_supplierForest_actual_040818
  · exact g32p_supplierForest_actual_040877
  · exact g32p_supplierForest_actual_041010
  · exact g32p_supplierForest_actual_041043
  · exact g32p_supplierForest_actual_041164
  · exact g32p_supplierForest_actual_041674
  · exact g32p_supplierForest_actual_041746
  · exact g32p_supplierForest_actual_041931
  · exact g32p_supplierForest_actual_042282
  · exact g32p_supplierForest_actual_042525
  · exact g32p_supplierForest_actual_042725
  · exact g32p_supplierForest_actual_042846
  · exact g32p_supplierForest_actual_043082
  · exact g32p_supplierForest_actual_043137
  · exact g32p_supplierForest_actual_043144
  · exact g32p_supplierForest_actual_043154
  · exact g32p_supplierForest_actual_043239
  · exact g32p_supplierForest_actual_043393
  · exact g32p_supplierForest_actual_043584
  · exact g32p_supplierForest_actual_043751
  · exact g32p_supplierForest_actual_043858
  · exact g32p_supplierForest_actual_043988
  · exact g32p_supplierForest_actual_044482
  · exact g32p_supplierForest_actual_044818
  · exact g32p_supplierForest_actual_044830
  · exact g32p_supplierForest_actual_044897
  · exact g32p_supplierForest_actual_045013
  · exact g32p_supplierForest_actual_045151
  · exact g32p_supplierForest_actual_045196
  · exact g32p_supplierForest_actual_045696
  · exact g32p_supplierForest_actual_046103
  · exact g32p_supplierForest_actual_046314
  · exact g32p_supplierForest_actual_046388
  · exact g32p_supplierForest_actual_046441
  · exact g32p_supplierForest_actual_046478
  · exact g32p_supplierForest_actual_046620
  · exact g32p_supplierForest_actual_046629
  · exact g32p_supplierForest_actual_046864
  · exact g32p_supplierForest_actual_046911
  · exact g32p_supplierForest_actual_047012
  · exact g32p_supplierForest_actual_047410
  · exact g32p_supplierForest_actual_047710
  · exact g32p_supplierForest_actual_047827
  · exact g32p_supplierForest_actual_048219
  · exact g32p_supplierForest_actual_048264
  · exact g32p_supplierForest_actual_048680
  · exact g32p_supplierForest_actual_048785
  · exact g32p_supplierForest_actual_049092
  · exact g32p_supplierForest_actual_049321
  · exact g32p_supplierForest_actual_049419
  · exact g32p_supplierForest_actual_049493
  · exact g32p_supplierForest_actual_049759
  · exact g32p_supplierForest_actual_050065

def g32p_supplierForest_nodes_143 : Fin 256 → HurwitzPrymRex_Mat :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then g32p_supplierForest_node_050154 else g32p_supplierForest_node_050263) else (if i.val < 3 then g32p_supplierForest_node_050380 else g32p_supplierForest_node_050600)) else (if i.val < 6 then (if i.val < 5 then g32p_supplierForest_node_050833 else g32p_supplierForest_node_051149) else (if i.val < 7 then g32p_supplierForest_node_051162 else g32p_supplierForest_node_051313))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then g32p_supplierForest_node_051459 else g32p_supplierForest_node_051622) else (if i.val < 11 then g32p_supplierForest_node_051875 else g32p_supplierForest_node_051989)) else (if i.val < 14 then (if i.val < 13 then g32p_supplierForest_node_052053 else g32p_supplierForest_node_052175) else (if i.val < 15 then g32p_supplierForest_node_052421 else g32p_supplierForest_node_052531)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then g32p_supplierForest_node_052736 else g32p_supplierForest_node_052967) else (if i.val < 19 then g32p_supplierForest_node_053144 else g32p_supplierForest_node_053194)) else (if i.val < 22 then (if i.val < 21 then g32p_supplierForest_node_053292 else g32p_supplierForest_node_053408) else (if i.val < 23 then g32p_supplierForest_node_053485 else g32p_supplierForest_node_053832))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then g32p_supplierForest_node_053975 else g32p_supplierForest_node_054307) else (if i.val < 27 then g32p_supplierForest_node_054435 else g32p_supplierForest_node_054536)) else (if i.val < 30 then (if i.val < 29 then g32p_supplierForest_node_054592 else g32p_supplierForest_node_054754) else (if i.val < 31 then g32p_supplierForest_node_055236 else g32p_supplierForest_node_055284))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then g32p_supplierForest_node_055571 else g32p_supplierForest_node_055576) else (if i.val < 35 then g32p_supplierForest_node_055824 else g32p_supplierForest_node_056533)) else (if i.val < 38 then (if i.val < 37 then g32p_supplierForest_node_056585 else g32p_supplierForest_node_056832) else (if i.val < 39 then g32p_supplierForest_node_056855 else g32p_supplierForest_node_057059))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then g32p_supplierForest_node_057880 else g32p_supplierForest_node_058240) else (if i.val < 43 then g32p_supplierForest_node_058326 else g32p_supplierForest_node_058327)) else (if i.val < 46 then (if i.val < 45 then g32p_supplierForest_node_058830 else g32p_supplierForest_node_058865) else (if i.val < 47 then g32p_supplierForest_node_059227 else g32p_supplierForest_node_059314)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then g32p_supplierForest_node_059341 else g32p_supplierForest_node_059428) else (if i.val < 51 then g32p_supplierForest_node_059706 else g32p_supplierForest_node_059732)) else (if i.val < 54 then (if i.val < 53 then g32p_supplierForest_node_059778 else g32p_supplierForest_node_059958) else (if i.val < 55 then g32p_supplierForest_node_060035 else g32p_supplierForest_node_060319))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then g32p_supplierForest_node_060531 else g32p_supplierForest_node_060988) else (if i.val < 59 then g32p_supplierForest_node_061339 else g32p_supplierForest_node_061371)) else (if i.val < 62 then (if i.val < 61 then g32p_supplierForest_node_061405 else g32p_supplierForest_node_061468) else (if i.val < 63 then g32p_supplierForest_node_061580 else g32p_supplierForest_node_061630)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then g32p_supplierForest_node_061638 else g32p_supplierForest_node_061670) else (if i.val < 67 then g32p_supplierForest_node_061709 else g32p_supplierForest_node_061716)) else (if i.val < 70 then (if i.val < 69 then g32p_supplierForest_node_061784 else g32p_supplierForest_node_061978) else (if i.val < 71 then g32p_supplierForest_node_062440 else g32p_supplierForest_node_062566))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then g32p_supplierForest_node_062742 else g32p_supplierForest_node_062896) else (if i.val < 75 then g32p_supplierForest_node_063016 else g32p_supplierForest_node_063119)) else (if i.val < 78 then (if i.val < 77 then g32p_supplierForest_node_063171 else g32p_supplierForest_node_063174) else (if i.val < 79 then g32p_supplierForest_node_063465 else g32p_supplierForest_node_063557)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then g32p_supplierForest_node_064004 else g32p_supplierForest_node_064176) else (if i.val < 83 then g32p_supplierForest_node_064231 else g32p_supplierForest_node_064621)) else (if i.val < 86 then (if i.val < 85 then g32p_supplierForest_node_064810 else g32p_supplierForest_node_064909) else (if i.val < 87 then g32p_supplierForest_node_065364 else g32p_supplierForest_node_065860))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then g32p_supplierForest_node_065996 else g32p_supplierForest_node_066288) else (if i.val < 91 then g32p_supplierForest_node_066456 else g32p_supplierForest_node_067095)) else (if i.val < 94 then (if i.val < 93 then g32p_supplierForest_node_067346 else g32p_supplierForest_node_067566) else (if i.val < 95 then g32p_supplierForest_node_067684 else g32p_supplierForest_node_067773))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then g32p_supplierForest_node_068159 else g32p_supplierForest_node_068167) else (if i.val < 99 then g32p_supplierForest_node_068173 else g32p_supplierForest_node_068188)) else (if i.val < 102 then (if i.val < 101 then g32p_supplierForest_node_068368 else g32p_supplierForest_node_068370) else (if i.val < 103 then g32p_supplierForest_node_068432 else g32p_supplierForest_node_068524))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then g32p_supplierForest_node_068706 else g32p_supplierForest_node_068834) else (if i.val < 107 then g32p_supplierForest_node_069017 else g32p_supplierForest_node_069077)) else (if i.val < 110 then (if i.val < 109 then g32p_supplierForest_node_069282 else g32p_supplierForest_node_069415) else (if i.val < 111 then g32p_supplierForest_node_069504 else g32p_supplierForest_node_069620)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then g32p_supplierForest_node_070051 else g32p_supplierForest_node_070445) else (if i.val < 115 then g32p_supplierForest_node_070496 else g32p_supplierForest_node_070618)) else (if i.val < 118 then (if i.val < 117 then g32p_supplierForest_node_070928 else g32p_supplierForest_node_070996) else (if i.val < 119 then g32p_supplierForest_node_071867 else g32p_supplierForest_node_071877))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then g32p_supplierForest_node_071945 else g32p_supplierForest_node_071978) else (if i.val < 123 then g32p_supplierForest_node_072105 else g32p_supplierForest_node_072628)) else (if i.val < 126 then (if i.val < 125 then g32p_supplierForest_node_073023 else g32p_supplierForest_node_073215) else (if i.val < 127 then g32p_supplierForest_node_073291 else g32p_supplierForest_node_073491))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then g32p_supplierForest_node_073637 else g32p_supplierForest_node_073789) else (if i.val < 131 then g32p_supplierForest_node_074230 else g32p_supplierForest_node_074299)) else (if i.val < 134 then (if i.val < 133 then g32p_supplierForest_node_074355 else g32p_supplierForest_node_075105) else (if i.val < 135 then g32p_supplierForest_node_075116 else g32p_supplierForest_node_075270))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then g32p_supplierForest_node_075568 else g32p_supplierForest_node_075613) else (if i.val < 139 then g32p_supplierForest_node_075740 else g32p_supplierForest_node_075759)) else (if i.val < 142 then (if i.val < 141 then g32p_supplierForest_node_075770 else g32p_supplierForest_node_075791) else (if i.val < 143 then g32p_supplierForest_node_075914 else g32p_supplierForest_node_076083)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then g32p_supplierForest_node_076168 else g32p_supplierForest_node_076176) else (if i.val < 147 then g32p_supplierForest_node_076282 else g32p_supplierForest_node_076507)) else (if i.val < 150 then (if i.val < 149 then g32p_supplierForest_node_076517 else g32p_supplierForest_node_076657) else (if i.val < 151 then g32p_supplierForest_node_076774 else g32p_supplierForest_node_077065))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then g32p_supplierForest_node_077217 else g32p_supplierForest_node_077483) else (if i.val < 155 then g32p_supplierForest_node_077641 else g32p_supplierForest_node_077645)) else (if i.val < 158 then (if i.val < 157 then g32p_supplierForest_node_077714 else g32p_supplierForest_node_077737) else (if i.val < 159 then g32p_supplierForest_node_077769 else g32p_supplierForest_node_077795))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then g32p_supplierForest_node_077880 else g32p_supplierForest_node_077998) else (if i.val < 163 then g32p_supplierForest_node_078073 else g32p_supplierForest_node_078522)) else (if i.val < 166 then (if i.val < 165 then g32p_supplierForest_node_078666 else g32p_supplierForest_node_078729) else (if i.val < 167 then g32p_supplierForest_node_078785 else g32p_supplierForest_node_078935))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then g32p_supplierForest_node_079151 else g32p_supplierForest_node_079194) else (if i.val < 171 then g32p_supplierForest_node_079219 else g32p_supplierForest_node_079224)) else (if i.val < 174 then (if i.val < 173 then g32p_supplierForest_node_079269 else g32p_supplierForest_node_079361) else (if i.val < 175 then g32p_supplierForest_node_079439 else g32p_supplierForest_node_079466)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then g32p_supplierForest_node_079491 else g32p_supplierForest_node_079498) else (if i.val < 179 then g32p_supplierForest_node_079547 else g32p_supplierForest_node_080053)) else (if i.val < 182 then (if i.val < 181 then g32p_supplierForest_node_080163 else g32p_supplierForest_node_080166) else (if i.val < 183 then g32p_supplierForest_node_080184 else g32p_supplierForest_node_080299))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then g32p_supplierForest_node_080333 else g32p_supplierForest_node_080421) else (if i.val < 187 then g32p_supplierForest_node_080425 else g32p_supplierForest_node_080504)) else (if i.val < 190 then (if i.val < 189 then g32p_supplierForest_node_080563 else g32p_supplierForest_node_080595) else (if i.val < 191 then g32p_supplierForest_node_080649 else g32p_supplierForest_node_080686)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then g32p_supplierForest_node_080773 else g32p_supplierForest_node_080824) else (if i.val < 195 then g32p_supplierForest_node_080879 else g32p_supplierForest_node_080962)) else (if i.val < 198 then (if i.val < 197 then g32p_supplierForest_node_081016 else g32p_supplierForest_node_081033) else (if i.val < 199 then g32p_supplierForest_node_081103 else g32p_supplierForest_node_081378))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then g32p_supplierForest_node_081593 else g32p_supplierForest_node_082292) else (if i.val < 203 then g32p_supplierForest_node_082713 else g32p_supplierForest_node_083423)) else (if i.val < 206 then (if i.val < 205 then g32p_supplierForest_node_083682 else g32p_supplierForest_node_084018) else (if i.val < 207 then g32p_supplierForest_node_084038 else g32p_supplierForest_node_084071)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then g32p_supplierForest_node_084474 else g32p_supplierForest_node_084731) else (if i.val < 211 then g32p_supplierForest_node_084798 else g32p_supplierForest_node_084807)) else (if i.val < 214 then (if i.val < 213 then g32p_supplierForest_node_084955 else g32p_supplierForest_node_085462) else (if i.val < 215 then g32p_supplierForest_node_085476 else g32p_supplierForest_node_085592))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then g32p_supplierForest_node_085801 else g32p_supplierForest_node_085815) else (if i.val < 219 then g32p_supplierForest_node_086441 else g32p_supplierForest_node_087004)) else (if i.val < 222 then (if i.val < 221 then g32p_supplierForest_node_087017 else g32p_supplierForest_node_087168) else (if i.val < 223 then g32p_supplierForest_node_087238 else g32p_supplierForest_node_087632))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then g32p_supplierForest_node_087908 else g32p_supplierForest_node_088174) else (if i.val < 227 then g32p_supplierForest_node_088268 else g32p_supplierForest_node_088303)) else (if i.val < 230 then (if i.val < 229 then g32p_supplierForest_node_088852 else g32p_supplierForest_node_088854) else (if i.val < 231 then g32p_supplierForest_node_088957 else g32p_supplierForest_node_088973))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then g32p_supplierForest_node_088980 else g32p_supplierForest_node_088982) else (if i.val < 235 then g32p_supplierForest_node_089647 else g32p_supplierForest_node_089989)) else (if i.val < 238 then (if i.val < 237 then g32p_supplierForest_node_090040 else g32p_supplierForest_node_090047) else (if i.val < 239 then g32p_supplierForest_node_090143 else g32p_supplierForest_node_090218)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then g32p_supplierForest_node_090355 else g32p_supplierForest_node_090400) else (if i.val < 243 then g32p_supplierForest_node_090504 else g32p_supplierForest_node_090576)) else (if i.val < 246 then (if i.val < 245 then g32p_supplierForest_node_090653 else g32p_supplierForest_node_090769) else (if i.val < 247 then g32p_supplierForest_node_090881 else g32p_supplierForest_node_091877))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then g32p_supplierForest_node_092285 else g32p_supplierForest_node_092762) else (if i.val < 251 then g32p_supplierForest_node_092912 else g32p_supplierForest_node_093009)) else (if i.val < 254 then (if i.val < 253 then g32p_supplierForest_node_093265 else g32p_supplierForest_node_093598) else (if i.val < 255 then g32p_supplierForest_node_093818 else g32p_supplierForest_node_093986))))))))

def g32p_supplierForest_classes_143 : Fin 256 → Fin 102 :=
  fun i => (if i.val < 128 then (if i.val < 64 then (if i.val < 32 then (if i.val < 16 then (if i.val < 8 then (if i.val < 4 then (if i.val < 2 then (if i.val < 1 then 68 else 38) else (if i.val < 3 then 38 else 38)) else (if i.val < 6 then (if i.val < 5 then 38 else 38) else (if i.val < 7 then 21 else 39))) else (if i.val < 12 then (if i.val < 10 then (if i.val < 9 then 38 else 39) else (if i.val < 11 then 38 else 21)) else (if i.val < 14 then (if i.val < 13 then 22 else 38) else (if i.val < 15 then 68 else 38)))) else (if i.val < 24 then (if i.val < 20 then (if i.val < 18 then (if i.val < 17 then 38 else 38) else (if i.val < 19 then 38 else 21)) else (if i.val < 22 then (if i.val < 21 then 22 else 21) else (if i.val < 23 then 38 else 38))) else (if i.val < 28 then (if i.val < 26 then (if i.val < 25 then 43 else 22) else (if i.val < 27 then 38 else 38)) else (if i.val < 30 then (if i.val < 29 then 21 else 38) else (if i.val < 31 then 38 else 22))))) else (if i.val < 48 then (if i.val < 40 then (if i.val < 36 then (if i.val < 34 then (if i.val < 33 then 38 else 20) else (if i.val < 35 then 39 else 21)) else (if i.val < 38 then (if i.val < 37 then 21 else 22) else (if i.val < 39 then 21 else 38))) else (if i.val < 44 then (if i.val < 42 then (if i.val < 41 then 21 else 38) else (if i.val < 43 then 38 else 21)) else (if i.val < 46 then (if i.val < 45 then 38 else 38) else (if i.val < 47 then 21 else 38)))) else (if i.val < 56 then (if i.val < 52 then (if i.val < 50 then (if i.val < 49 then 38 else 38) else (if i.val < 51 then 38 else 21)) else (if i.val < 54 then (if i.val < 53 then 73 else 21) else (if i.val < 55 then 73 else 38))) else (if i.val < 60 then (if i.val < 58 then (if i.val < 57 then 38 else 38) else (if i.val < 59 then 38 else 21)) else (if i.val < 62 then (if i.val < 61 then 38 else 72) else (if i.val < 63 then 20 else 21)))))) else (if i.val < 96 then (if i.val < 80 then (if i.val < 72 then (if i.val < 68 then (if i.val < 66 then (if i.val < 65 then 21 else 38) else (if i.val < 67 then 21 else 21)) else (if i.val < 70 then (if i.val < 69 then 21 else 21) else (if i.val < 71 then 21 else 21))) else (if i.val < 76 then (if i.val < 74 then (if i.val < 73 then 21 else 20) else (if i.val < 75 then 22 else 38)) else (if i.val < 78 then (if i.val < 77 then 41 else 38) else (if i.val < 79 then 22 else 21)))) else (if i.val < 88 then (if i.val < 84 then (if i.val < 82 then (if i.val < 81 then 41 else 21) else (if i.val < 83 then 70 else 21)) else (if i.val < 86 then (if i.val < 85 then 38 else 38) else (if i.val < 87 then 22 else 38))) else (if i.val < 92 then (if i.val < 90 then (if i.val < 89 then 68 else 21) else (if i.val < 91 then 21 else 38)) else (if i.val < 94 then (if i.val < 93 then 38 else 38) else (if i.val < 95 then 38 else 22))))) else (if i.val < 112 then (if i.val < 104 then (if i.val < 100 then (if i.val < 98 then (if i.val < 97 then 38 else 73) else (if i.val < 99 then 38 else 21)) else (if i.val < 102 then (if i.val < 101 then 38 else 21) else (if i.val < 103 then 38 else 21))) else (if i.val < 108 then (if i.val < 106 then (if i.val < 105 then 38 else 22) else (if i.val < 107 then 38 else 21)) else (if i.val < 110 then (if i.val < 109 then 38 else 38) else (if i.val < 111 then 70 else 21)))) else (if i.val < 120 then (if i.val < 116 then (if i.val < 114 then (if i.val < 113 then 73 else 21) else (if i.val < 115 then 38 else 73)) else (if i.val < 118 then (if i.val < 117 then 73 else 42) else (if i.val < 119 then 49 else 49))) else (if i.val < 124 then (if i.val < 122 then (if i.val < 121 then 49 else 26) else (if i.val < 123 then 49 else 49)) else (if i.val < 126 then (if i.val < 125 then 49 else 49) else (if i.val < 127 then 49 else 26))))))) else (if i.val < 192 then (if i.val < 160 then (if i.val < 144 then (if i.val < 136 then (if i.val < 132 then (if i.val < 130 then (if i.val < 129 then 49 else 26) else (if i.val < 131 then 46 else 49)) else (if i.val < 134 then (if i.val < 133 then 49 else 49) else (if i.val < 135 then 49 else 46))) else (if i.val < 140 then (if i.val < 138 then (if i.val < 137 then 49 else 46) else (if i.val < 139 then 47 else 49)) else (if i.val < 142 then (if i.val < 141 then 49 else 46) else (if i.val < 143 then 49 else 49)))) else (if i.val < 152 then (if i.val < 148 then (if i.val < 146 then (if i.val < 145 then 46 else 49) else (if i.val < 147 then 46 else 54)) else (if i.val < 150 then (if i.val < 149 then 49 else 49) else (if i.val < 151 then 47 else 49))) else (if i.val < 156 then (if i.val < 154 then (if i.val < 153 then 46 else 49) else (if i.val < 155 then 46 else 46)) else (if i.val < 158 then (if i.val < 157 then 26 else 50) else (if i.val < 159 then 49 else 49))))) else (if i.val < 176 then (if i.val < 168 then (if i.val < 164 then (if i.val < 162 then (if i.val < 161 then 53 else 47) else (if i.val < 163 then 49 else 49)) else (if i.val < 166 then (if i.val < 165 then 49 else 26) else (if i.val < 167 then 47 else 47))) else (if i.val < 172 then (if i.val < 170 then (if i.val < 169 then 26 else 49) else (if i.val < 171 then 47 else 47)) else (if i.val < 174 then (if i.val < 173 then 26 else 49) else (if i.val < 175 then 46 else 49)))) else (if i.val < 184 then (if i.val < 180 then (if i.val < 178 then (if i.val < 177 then 54 else 49) else (if i.val < 179 then 49 else 49)) else (if i.val < 182 then (if i.val < 181 then 49 else 50) else (if i.val < 183 then 47 else 49))) else (if i.val < 188 then (if i.val < 186 then (if i.val < 185 then 49 else 53) else (if i.val < 187 then 49 else 46)) else (if i.val < 190 then (if i.val < 189 then 46 else 49) else (if i.val < 191 then 49 else 49)))))) else (if i.val < 224 then (if i.val < 208 then (if i.val < 200 then (if i.val < 196 then (if i.val < 194 then (if i.val < 193 then 49 else 49) else (if i.val < 195 then 49 else 49)) else (if i.val < 198 then (if i.val < 197 then 54 else 49) else (if i.val < 199 then 49 else 49))) else (if i.val < 204 then (if i.val < 202 then (if i.val < 201 then 49 else 26) else (if i.val < 203 then 46 else 49)) else (if i.val < 206 then (if i.val < 205 then 49 else 46) else (if i.val < 207 then 49 else 49)))) else (if i.val < 216 then (if i.val < 212 then (if i.val < 210 then (if i.val < 209 then 49 else 47) else (if i.val < 211 then 49 else 55)) else (if i.val < 214 then (if i.val < 213 then 46 else 26) else (if i.val < 215 then 47 else 49))) else (if i.val < 220 then (if i.val < 218 then (if i.val < 217 then 9 else 25) else (if i.val < 219 then 47 else 49)) else (if i.val < 222 then (if i.val < 221 then 47 else 46) else (if i.val < 223 then 49 else 46))))) else (if i.val < 240 then (if i.val < 232 then (if i.val < 228 then (if i.val < 226 then (if i.val < 225 then 47 else 46) else (if i.val < 227 then 26 else 49)) else (if i.val < 230 then (if i.val < 229 then 46 else 46) else (if i.val < 231 then 47 else 49))) else (if i.val < 236 then (if i.val < 234 then (if i.val < 233 then 47 else 46) else (if i.val < 235 then 46 else 46)) else (if i.val < 238 then (if i.val < 237 then 49 else 49) else (if i.val < 239 then 49 else 26)))) else (if i.val < 248 then (if i.val < 244 then (if i.val < 242 then (if i.val < 241 then 49 else 49) else (if i.val < 243 then 49 else 49)) else (if i.val < 246 then (if i.val < 245 then 49 else 46) else (if i.val < 247 then 46 else 50))) else (if i.val < 252 then (if i.val < 250 then (if i.val < 249 then 49 else 26) else (if i.val < 251 then 46 else 49)) else (if i.val < 254 then (if i.val < 253 then 26 else 46) else (if i.val < 255 then 47 else 46))))))))

theorem g32p_supplierForest_actual_143 (i : Fin 256) :
    ∃ g : g32p_G,
      b4b_toMatrix g = HurwitzPrymRex_g32conj
        (HurwitzPrymRex_evM g32h_omega (g32p_supplierForest_nodes_143 i)) ∧
      IsConj g (g32p_literalRepresentative (g32p_supplierForest_classes_143 i)) := by
  fin_cases i
  · exact g32p_supplierForest_actual_050154
  · exact g32p_supplierForest_actual_050263
  · exact g32p_supplierForest_actual_050380
  · exact g32p_supplierForest_actual_050600
  · exact g32p_supplierForest_actual_050833
  · exact g32p_supplierForest_actual_051149
  · exact g32p_supplierForest_actual_051162
  · exact g32p_supplierForest_actual_051313
  · exact g32p_supplierForest_actual_051459
  · exact g32p_supplierForest_actual_051622
  · exact g32p_supplierForest_actual_051875
  · exact g32p_supplierForest_actual_051989
  · exact g32p_supplierForest_actual_052053
  · exact g32p_supplierForest_actual_052175
  · exact g32p_supplierForest_actual_052421
  · exact g32p_supplierForest_actual_052531
  · exact g32p_supplierForest_actual_052736
  · exact g32p_supplierForest_actual_052967
  · exact g32p_supplierForest_actual_053144
  · exact g32p_supplierForest_actual_053194
  · exact g32p_supplierForest_actual_053292
  · exact g32p_supplierForest_actual_053408
  · exact g32p_supplierForest_actual_053485
  · exact g32p_supplierForest_actual_053832
  · exact g32p_supplierForest_actual_053975
  · exact g32p_supplierForest_actual_054307
  · exact g32p_supplierForest_actual_054435
  · exact g32p_supplierForest_actual_054536
  · exact g32p_supplierForest_actual_054592
  · exact g32p_supplierForest_actual_054754
  · exact g32p_supplierForest_actual_055236
  · exact g32p_supplierForest_actual_055284
  · exact g32p_supplierForest_actual_055571
  · exact g32p_supplierForest_actual_055576
  · exact g32p_supplierForest_actual_055824
  · exact g32p_supplierForest_actual_056533
  · exact g32p_supplierForest_actual_056585
  · exact g32p_supplierForest_actual_056832
  · exact g32p_supplierForest_actual_056855
  · exact g32p_supplierForest_actual_057059
  · exact g32p_supplierForest_actual_057880
  · exact g32p_supplierForest_actual_058240
  · exact g32p_supplierForest_actual_058326
  · exact g32p_supplierForest_actual_058327
  · exact g32p_supplierForest_actual_058830
  · exact g32p_supplierForest_actual_058865
  · exact g32p_supplierForest_actual_059227
  · exact g32p_supplierForest_actual_059314
  · exact g32p_supplierForest_actual_059341
  · exact g32p_supplierForest_actual_059428
  · exact g32p_supplierForest_actual_059706
  · exact g32p_supplierForest_actual_059732
  · exact g32p_supplierForest_actual_059778
  · exact g32p_supplierForest_actual_059958
  · exact g32p_supplierForest_actual_060035
  · exact g32p_supplierForest_actual_060319
  · exact g32p_supplierForest_actual_060531
  · exact g32p_supplierForest_actual_060988
  · exact g32p_supplierForest_actual_061339
  · exact g32p_supplierForest_actual_061371
  · exact g32p_supplierForest_actual_061405
  · exact g32p_supplierForest_actual_061468
  · exact g32p_supplierForest_actual_061580
  · exact g32p_supplierForest_actual_061630
  · exact g32p_supplierForest_actual_061638
  · exact g32p_supplierForest_actual_061670
  · exact g32p_supplierForest_actual_061709
  · exact g32p_supplierForest_actual_061716
  · exact g32p_supplierForest_actual_061784
  · exact g32p_supplierForest_actual_061978
  · exact g32p_supplierForest_actual_062440
  · exact g32p_supplierForest_actual_062566
  · exact g32p_supplierForest_actual_062742
  · exact g32p_supplierForest_actual_062896
  · exact g32p_supplierForest_actual_063016
  · exact g32p_supplierForest_actual_063119
  · exact g32p_supplierForest_actual_063171
  · exact g32p_supplierForest_actual_063174
  · exact g32p_supplierForest_actual_063465
  · exact g32p_supplierForest_actual_063557
  · exact g32p_supplierForest_actual_064004
  · exact g32p_supplierForest_actual_064176
  · exact g32p_supplierForest_actual_064231
  · exact g32p_supplierForest_actual_064621
  · exact g32p_supplierForest_actual_064810
  · exact g32p_supplierForest_actual_064909
  · exact g32p_supplierForest_actual_065364
  · exact g32p_supplierForest_actual_065860
  · exact g32p_supplierForest_actual_065996
  · exact g32p_supplierForest_actual_066288
  · exact g32p_supplierForest_actual_066456
  · exact g32p_supplierForest_actual_067095
  · exact g32p_supplierForest_actual_067346
  · exact g32p_supplierForest_actual_067566
  · exact g32p_supplierForest_actual_067684
  · exact g32p_supplierForest_actual_067773
  · exact g32p_supplierForest_actual_068159
  · exact g32p_supplierForest_actual_068167
  · exact g32p_supplierForest_actual_068173
  · exact g32p_supplierForest_actual_068188
  · exact g32p_supplierForest_actual_068368
  · exact g32p_supplierForest_actual_068370
  · exact g32p_supplierForest_actual_068432
  · exact g32p_supplierForest_actual_068524
  · exact g32p_supplierForest_actual_068706
  · exact g32p_supplierForest_actual_068834
  · exact g32p_supplierForest_actual_069017
  · exact g32p_supplierForest_actual_069077
  · exact g32p_supplierForest_actual_069282
  · exact g32p_supplierForest_actual_069415
  · exact g32p_supplierForest_actual_069504
  · exact g32p_supplierForest_actual_069620
  · exact g32p_supplierForest_actual_070051
  · exact g32p_supplierForest_actual_070445
  · exact g32p_supplierForest_actual_070496
  · exact g32p_supplierForest_actual_070618
  · exact g32p_supplierForest_actual_070928
  · exact g32p_supplierForest_actual_070996
  · exact g32p_supplierForest_actual_071867
  · exact g32p_supplierForest_actual_071877
  · exact g32p_supplierForest_actual_071945
  · exact g32p_supplierForest_actual_071978
  · exact g32p_supplierForest_actual_072105
  · exact g32p_supplierForest_actual_072628
  · exact g32p_supplierForest_actual_073023
  · exact g32p_supplierForest_actual_073215
  · exact g32p_supplierForest_actual_073291
  · exact g32p_supplierForest_actual_073491
  · exact g32p_supplierForest_actual_073637
  · exact g32p_supplierForest_actual_073789
  · exact g32p_supplierForest_actual_074230
  · exact g32p_supplierForest_actual_074299
  · exact g32p_supplierForest_actual_074355
  · exact g32p_supplierForest_actual_075105
  · exact g32p_supplierForest_actual_075116
  · exact g32p_supplierForest_actual_075270
  · exact g32p_supplierForest_actual_075568
  · exact g32p_supplierForest_actual_075613
  · exact g32p_supplierForest_actual_075740
  · exact g32p_supplierForest_actual_075759
  · exact g32p_supplierForest_actual_075770
  · exact g32p_supplierForest_actual_075791
  · exact g32p_supplierForest_actual_075914
  · exact g32p_supplierForest_actual_076083
  · exact g32p_supplierForest_actual_076168
  · exact g32p_supplierForest_actual_076176
  · exact g32p_supplierForest_actual_076282
  · exact g32p_supplierForest_actual_076507
  · exact g32p_supplierForest_actual_076517
  · exact g32p_supplierForest_actual_076657
  · exact g32p_supplierForest_actual_076774
  · exact g32p_supplierForest_actual_077065
  · exact g32p_supplierForest_actual_077217
  · exact g32p_supplierForest_actual_077483
  · exact g32p_supplierForest_actual_077641
  · exact g32p_supplierForest_actual_077645
  · exact g32p_supplierForest_actual_077714
  · exact g32p_supplierForest_actual_077737
  · exact g32p_supplierForest_actual_077769
  · exact g32p_supplierForest_actual_077795
  · exact g32p_supplierForest_actual_077880
  · exact g32p_supplierForest_actual_077998
  · exact g32p_supplierForest_actual_078073
  · exact g32p_supplierForest_actual_078522
  · exact g32p_supplierForest_actual_078666
  · exact g32p_supplierForest_actual_078729
  · exact g32p_supplierForest_actual_078785
  · exact g32p_supplierForest_actual_078935
  · exact g32p_supplierForest_actual_079151
  · exact g32p_supplierForest_actual_079194
  · exact g32p_supplierForest_actual_079219
  · exact g32p_supplierForest_actual_079224
  · exact g32p_supplierForest_actual_079269
  · exact g32p_supplierForest_actual_079361
  · exact g32p_supplierForest_actual_079439
  · exact g32p_supplierForest_actual_079466
  · exact g32p_supplierForest_actual_079491
  · exact g32p_supplierForest_actual_079498
  · exact g32p_supplierForest_actual_079547
  · exact g32p_supplierForest_actual_080053
  · exact g32p_supplierForest_actual_080163
  · exact g32p_supplierForest_actual_080166
  · exact g32p_supplierForest_actual_080184
  · exact g32p_supplierForest_actual_080299
  · exact g32p_supplierForest_actual_080333
  · exact g32p_supplierForest_actual_080421
  · exact g32p_supplierForest_actual_080425
  · exact g32p_supplierForest_actual_080504
  · exact g32p_supplierForest_actual_080563
  · exact g32p_supplierForest_actual_080595
  · exact g32p_supplierForest_actual_080649
  · exact g32p_supplierForest_actual_080686
  · exact g32p_supplierForest_actual_080773
  · exact g32p_supplierForest_actual_080824
  · exact g32p_supplierForest_actual_080879
  · exact g32p_supplierForest_actual_080962
  · exact g32p_supplierForest_actual_081016
  · exact g32p_supplierForest_actual_081033
  · exact g32p_supplierForest_actual_081103
  · exact g32p_supplierForest_actual_081378
  · exact g32p_supplierForest_actual_081593
  · exact g32p_supplierForest_actual_082292
  · exact g32p_supplierForest_actual_082713
  · exact g32p_supplierForest_actual_083423
  · exact g32p_supplierForest_actual_083682
  · exact g32p_supplierForest_actual_084018
  · exact g32p_supplierForest_actual_084038
  · exact g32p_supplierForest_actual_084071
  · exact g32p_supplierForest_actual_084474
  · exact g32p_supplierForest_actual_084731
  · exact g32p_supplierForest_actual_084798
  · exact g32p_supplierForest_actual_084807
  · exact g32p_supplierForest_actual_084955
  · exact g32p_supplierForest_actual_085462
  · exact g32p_supplierForest_actual_085476
  · exact g32p_supplierForest_actual_085592
  · exact g32p_supplierForest_actual_085801
  · exact g32p_supplierForest_actual_085815
  · exact g32p_supplierForest_actual_086441
  · exact g32p_supplierForest_actual_087004
  · exact g32p_supplierForest_actual_087017
  · exact g32p_supplierForest_actual_087168
  · exact g32p_supplierForest_actual_087238
  · exact g32p_supplierForest_actual_087632
  · exact g32p_supplierForest_actual_087908
  · exact g32p_supplierForest_actual_088174
  · exact g32p_supplierForest_actual_088268
  · exact g32p_supplierForest_actual_088303
  · exact g32p_supplierForest_actual_088852
  · exact g32p_supplierForest_actual_088854
  · exact g32p_supplierForest_actual_088957
  · exact g32p_supplierForest_actual_088973
  · exact g32p_supplierForest_actual_088980
  · exact g32p_supplierForest_actual_088982
  · exact g32p_supplierForest_actual_089647
  · exact g32p_supplierForest_actual_089989
  · exact g32p_supplierForest_actual_090040
  · exact g32p_supplierForest_actual_090047
  · exact g32p_supplierForest_actual_090143
  · exact g32p_supplierForest_actual_090218
  · exact g32p_supplierForest_actual_090355
  · exact g32p_supplierForest_actual_090400
  · exact g32p_supplierForest_actual_090504
  · exact g32p_supplierForest_actual_090576
  · exact g32p_supplierForest_actual_090653
  · exact g32p_supplierForest_actual_090769
  · exact g32p_supplierForest_actual_090881
  · exact g32p_supplierForest_actual_091877
  · exact g32p_supplierForest_actual_092285
  · exact g32p_supplierForest_actual_092762
  · exact g32p_supplierForest_actual_092912
  · exact g32p_supplierForest_actual_093009
  · exact g32p_supplierForest_actual_093265
  · exact g32p_supplierForest_actual_093598
  · exact g32p_supplierForest_actual_093818
  · exact g32p_supplierForest_actual_093986

end HodgeLean.Foundations.Program

end
end
