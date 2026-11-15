import HodgeLean.Foundations.Program.G32PropFourSixPacked0361
import HodgeLean.Foundations.Program.G32PropFourSixPacked0209
import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixSupplierRows
import HodgeLean.Foundations.Program.G32PropFourSixPacked0191
import HodgeLean.Foundations.Program.G32PropFourSixLiteralReconstructionData

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_02 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 2 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 2 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 2 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_02 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 2 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 2 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 2 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_02 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 2 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 2 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 2 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_02 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 2 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 2 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 2 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 2 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 2 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_03 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 3 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 3 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 3 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_03 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 3 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 3 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 3 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_03 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 3 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 3 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 3 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_03 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 3 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 3 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 3 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 3 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 3 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_04 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 4 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 4 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 4 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_04 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 4 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 4 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 4 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_04 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 4 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 4 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 4 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_04 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 4 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 4 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 4 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 4 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 4 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_05 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 5 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 5 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 5 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_05 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 5 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 5 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 5 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_05 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 5 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 5 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 5 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_05 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 5 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 5 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 5 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 5 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 5 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_06 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 6 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 6 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 6 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_06 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 6 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 6 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 6 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_06 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 6 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 6 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 6 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_06 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 6 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 6 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 6 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 6 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 6 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_07 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 7 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 7 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 7 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_07 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 7 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 7 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 7 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_07 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 7 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 7 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 7 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_07 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 7 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 7 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 7 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 7 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 7 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root_block_08 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 8 r) = 0 →
      g32p_row13_archiveNodes (g32p_finBlockIndex 134 8 r) = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass (g32p_finBlockIndex 134 8 r)) := by
  decide +kernel

theorem g32p_row13_archive_depth_block_08 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 8 r) ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent (g32p_finBlockIndex 134 8 r)) < g32p_row13_archiveDepth (g32p_finBlockIndex 134 8 r) := by
  decide +kernel

theorem g32p_row13_archive_class_block_08 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 8 r) ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent (g32p_finBlockIndex 134 8 r)) = g32p_row13_archiveClass (g32p_finBlockIndex 134 8 r) := by
  decide +kernel

theorem g32p_row13_archive_step_block_08 : ∀ r : Fin 16,
    g32p_row13_archiveDepth (g32p_finBlockIndex 134 8 r) ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes (g32p_finBlockIndex 134 8 r))
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 8 r))) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel (g32p_finBlockIndex 134 8 r)))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent (g32p_finBlockIndex 134 8 r))) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_archive_root (i : Fin 134) :
    g32p_row13_archiveDepth i = 0 →
      g32p_row13_archiveNodes i = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass i) := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row13_archiveDepth i = 0 →
      g32p_row13_archiveNodes i = g32p_literalRepresentativeMatrix (g32p_row13_archiveClass i)) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row13_archive_root_block_00 r
  · exact g32p_row13_archive_root_block_01 r
  · exact g32p_row13_archive_root_block_02 r
  · exact g32p_row13_archive_root_block_03 r
  · exact g32p_row13_archive_root_block_04 r
  · exact g32p_row13_archive_root_block_05 r
  · exact g32p_row13_archive_root_block_06 r
  · exact g32p_row13_archive_root_block_07 r
  · exact g32p_row13_archive_root_block_08 r

theorem g32p_row13_archive_depth (i : Fin 134) :
    g32p_row13_archiveDepth i ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent i) < g32p_row13_archiveDepth i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row13_archiveDepth i ≠ 0 →
      g32p_row13_archiveDepth (g32p_row13_archiveParent i) < g32p_row13_archiveDepth i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row13_archive_depth_block_00 r
  · exact g32p_row13_archive_depth_block_01 r
  · exact g32p_row13_archive_depth_block_02 r
  · exact g32p_row13_archive_depth_block_03 r
  · exact g32p_row13_archive_depth_block_04 r
  · exact g32p_row13_archive_depth_block_05 r
  · exact g32p_row13_archive_depth_block_06 r
  · exact g32p_row13_archive_depth_block_07 r
  · exact g32p_row13_archive_depth_block_08 r

theorem g32p_row13_archive_class (i : Fin 134) :
    g32p_row13_archiveDepth i ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent i) = g32p_row13_archiveClass i := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row13_archiveDepth i ≠ 0 →
      g32p_row13_archiveClass (g32p_row13_archiveParent i) = g32p_row13_archiveClass i) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row13_archive_class_block_00 r
  · exact g32p_row13_archive_class_block_01 r
  · exact g32p_row13_archive_class_block_02 r
  · exact g32p_row13_archive_class_block_03 r
  · exact g32p_row13_archive_class_block_04 r
  · exact g32p_row13_archive_class_block_05 r
  · exact g32p_row13_archive_class_block_06 r
  · exact g32p_row13_archive_class_block_07 r
  · exact g32p_row13_archive_class_block_08 r

theorem g32p_row13_archive_step (i : Fin 134) :
    g32p_row13_archiveDepth i ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes i)
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel i)) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel i))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent i)) := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_row13_archiveDepth i ≠ 0 →
      HurwitzPrymRex_mmul (g32p_row13_archiveNodes i)
        (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel i)) =
      HurwitzPrymRex_mmul (g32p_archiveIntegralGenerators (g32p_row13_archiveLabel i))
        (g32p_row13_archiveNodes (g32p_row13_archiveParent i))) ?_ i
  intro q r
  fin_cases q
  · exact g32p_row13_archive_step_block_00 r
  · exact g32p_row13_archive_step_block_01 r
  · exact g32p_row13_archive_step_block_02 r
  · exact g32p_row13_archive_step_block_03 r
  · exact g32p_row13_archive_step_block_04 r
  · exact g32p_row13_archive_step_block_05 r
  · exact g32p_row13_archive_step_block_06 r
  · exact g32p_row13_archive_step_block_07 r
  · exact g32p_row13_archive_step_block_08 r

theorem g32p_row13_archiveSource_map (i : Fin 24) :
    g32p_row13_archiveNodes (g32p_row13_archiveSourceIndex i) = g32p_row13_groupNodes i := by
  fin_cases i <;> decide +kernel

theorem g32p_row13_archiveSource_class : ∀ i : Fin 24,
    g32p_row13_archiveClass (g32p_row13_archiveSourceIndex i) =
      g32p_row13_supplierClassifier i := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

theorem g32p_row13_groupEquiv_isConj (i : Fin 24) :
    IsConj (g32p_row13_groupEquiv i : g32p_G)
      (g32p_literalRepresentative (g32p_row13_supplierClassifier i)) := by
  obtain ⟨g, hg, hc⟩ := g32p_archiveForest_lift
    g32p_row13_archiveNodes g32p_row13_archiveClass g32p_row13_archiveParent
    g32p_row13_archiveDepth g32p_row13_archiveLabel
    g32p_row13_archive_root g32p_row13_archive_depth g32p_row13_archive_class
    g32p_row13_archive_step (g32p_row13_archiveSourceIndex i)
  have he : (g32p_row13_groupEquiv i : g32p_G) = g := by
    apply Subtype.val_injective
    change b4b_toMatrix (g32p_row13_groupEquiv i : g32p_G) = b4b_toMatrix g
    rw [g32p_row13_groupEquiv_map, hg, g32p_row13_archiveSource_map]
  rw [g32p_row13_archiveSource_class] at hc
  exact he.symm ▸ hc

def g32p_row13_supplierClass (h : (g32p_recordedSuppliers 12).H) : Fin 102 :=
  g32p_row13_supplierClassifier (g32p_row13_groupEquiv.symm h)

theorem g32p_row13_supplierClass_isConj (h : (g32p_recordedSuppliers 12).H) :
    IsConj (h : g32p_G) (g32p_literalRepresentative (g32p_row13_supplierClass h)) := by
  have he : (g32p_row13_groupEquiv (g32p_row13_groupEquiv.symm h) : g32p_G) = (h : g32p_G) :=
    congrArg (fun a : g32p_row13_subgroup => (a : g32p_G))
      (g32p_row13_groupEquiv.apply_symm_apply h)
  change IsConj (h : g32p_G) (g32p_literalRepresentative
    (g32p_row13_supplierClassifier (g32p_row13_groupEquiv.symm h)))
  rw [← he]
  exact g32p_row13_groupEquiv_isConj (g32p_row13_groupEquiv.symm h)

theorem g32p_row13_supplierClass_iff (h : (g32p_recordedSuppliers 12).H) (c : Fin 102) :
    IsConj (g32p_literalRepresentative c) (h : g32p_G) ↔ c = g32p_row13_supplierClass h := by
  constructor
  · intro hc
    apply g32p_literalRepresentative_classes_injective
    exact ConjClasses.mk_eq_mk_iff_isConj.mpr (hc.trans (g32p_row13_supplierClass_isConj h))
  · intro hc
    rw [hc]
    exact (g32p_row13_supplierClass_isConj h).symm

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

def g32p_row13_classSupport : Finset (Fin 102) :=
  Finset.univ.image g32p_row13_supplierClassifier

theorem g32p_row13_classSupport_card : g32p_row13_classSupport.card = 17 := by
  decide +kernel

def g32p_row13_generatorIndex : Fin 8 → Fin 408 :=
  ![12, 63, 114, 165, 228, 229, 330, 331]

theorem g32p_row13_supplierClass_mem_support (h : (g32p_recordedSuppliers 12).H) :
    g32p_row13_supplierClass h ∈ g32p_row13_classSupport := by
  exact Finset.mem_image.mpr ⟨g32p_row13_groupEquiv.symm h, Finset.mem_univ _, rfl⟩

theorem g32p_row13_coinduced_zero (c : Fin 102) (hc : c ∉ g32p_row13_classSupport)
    (conjugate : Bool) :
    (g32p_recordedCoinduced 12 conjugate).character (g32p_literalRepresentative c) = 0 := by
  classical
  have hconj (h : (g32p_recordedSuppliers 12).H) :
      ¬ IsConj (g32p_literalRepresentative c) (h : g32p_G) := by
    intro hh
    apply hc
    rw [(g32p_row13_supplierClass_iff h c).mp hh]
    exact g32p_row13_supplierClass_mem_support h
  have hx (x : g32p_G) :
      x * g32p_literalRepresentative c * x⁻¹ ∉ (g32p_recordedSuppliers 12).H := by
    intro hm
    exact hconj ⟨_, hm⟩ (isConj_iff.mpr ⟨x, rfl⟩)
  rw [g32p_recordedCoinduced_character]
  simp [hx]

theorem g32p_row13_inductionGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_row13_classSupport) (conjugate : Bool) (variant : Fin 4) :
    (g32p_inductionGenerator 12 conjugate variant).character
      (g32p_literalRepresentative c) = 0 := by
  have h := g32p_row13_coinduced_zero c hc conjugate
  fin_cases variant <;>
    simp [g32p_inductionGenerator, FDRep.char_tensor, g32p_twist_character, h]

theorem g32p_row13_recordedGenerator_zero (c : Fin 102)
    (hc : c ∉ g32p_row13_classSupport) (k : Fin 8) :
    (g32p_recordedInductionGenerators (g32p_row13_generatorIndex k)).character
      (g32p_literalRepresentative c) = 0 := by
  fin_cases k
  · exact g32p_row13_inductionGenerator_zero c hc false 0
  · exact g32p_row13_inductionGenerator_zero c hc true 0
  · exact g32p_row13_inductionGenerator_zero c hc false 1
  · exact g32p_row13_inductionGenerator_zero c hc true 1
  · exact g32p_row13_inductionGenerator_zero c hc false 2
  · exact g32p_row13_inductionGenerator_zero c hc false 3
  · exact g32p_row13_inductionGenerator_zero c hc true 2
  · exact g32p_row13_inductionGenerator_zero c hc true 3

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_block_00 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 0 r ∉ g32p_row13_classSupport →
      g32p_literalTraceValue (g32p_row13_generatorIndex k) (g32p_finBlockIndex 102 0 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_block_01 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 1 r ∉ g32p_row13_classSupport →
      g32p_literalTraceValue (g32p_row13_generatorIndex k) (g32p_finBlockIndex 102 1 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_block_02 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 2 r ∉ g32p_row13_classSupport →
      g32p_literalTraceValue (g32p_row13_generatorIndex k) (g32p_finBlockIndex 102 2 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_block_03 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 3 r ∉ g32p_row13_classSupport →
      g32p_literalTraceValue (g32p_row13_generatorIndex k) (g32p_finBlockIndex 102 3 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_block_04 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 4 r ∉ g32p_row13_classSupport →
      g32p_literalTraceValue (g32p_row13_generatorIndex k) (g32p_finBlockIndex 102 4 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
set_option maxHeartbeats 400000
set_option maxRecDepth 2048

theorem g32p_row13_zeroTrace_block_05 : ∀ (r : Fin 16) (k : Fin 8),
    g32p_finBlockIndex 102 5 r ∉ g32p_row13_classSupport →
      g32p_literalTraceValue (g32p_row13_generatorIndex k) (g32p_finBlockIndex 102 5 r) =
        (⟨0, 0⟩ : HurwitzPrymRex_Zw) := by
  decide +kernel

end HodgeLean.Foundations.Program

end
end
