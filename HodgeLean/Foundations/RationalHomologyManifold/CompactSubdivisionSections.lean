import HodgeLean.Foundations.RationalHomologyManifold.AmbientSubdivisionSections
import HodgeLean.Foundations.RationalHomologyManifold.CompactChainPatches

/-! Finite common-stage representatives around compact supports.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace AlgebraicTopology.Singular
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- A subdivision-limit section near a compact set has finitely many actual ambient representatives at one common stage.
Source: Bredon, Sheaf Theory, second edition, VI.12; finite supported-chain representatives near compact sets.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_compact_common_stage (X : TopCat.{0}) (n : ℕ)
    (K : Set X) (hK : IsCompact K) (U : Opens X) (hKU : K ⊆ U)
    (s : ((subdivisionLimitSheafComplex X).X n).obj.obj (Opposite.op U)) :
    ∃ (I : Finset K) (W : I → Opens X) (hW : ∀ i, W i ≤ U)
      (M : ℕ) (z : I → (SingularChainComplex ℚ X).X n),
      (∀ x ∈ K, ∃ i, x ∈ W i) ∧ ∀ i,
        (subdivisionAmbientSectionMap X n (W i) M).hom (z i) =
          ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE (hW i)).op s := by
  classical
  have hloc (x : K) : ∃ (V : Opens X) (hV : V ≤ U) (m : ℕ)
      (z : (SingularChainComplex ℚ X).X n), x.val ∈ V ∧
      (subdivisionAmbientSectionMap X n V m).hom z =
        ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE hV).op s := by
    obtain ⟨V, hV, m, z, hxV, hz⟩ :=
      subdivisionLimitSheaf_section_locally_ambient X n U s x.val (hKU x.property)
    exact ⟨V, hV, m, z, hxV, hz⟩
  choose V hV m z hxV hz using hloc
  have hcover : K ⊆ ⋃ x : K, (V x : Set X) := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, hxV ⟨x, hx⟩⟩
  obtain ⟨I, hI⟩ := hK.elim_finite_subcover (fun x : K => (V x : Set X))
    (fun x => (V x).isOpen) hcover
  let M := I.sup m
  let z' (i : I) : (SingularChainComplex ℚ X).X n :=
    (rationalSubdivisionIterate X (M - m i)).f n (z i)
  refine ⟨I, (fun i => V i), (fun i => hV i), M, z', ?_, ?_⟩
  · intro x hx
    obtain ⟨i, hi⟩ := Set.mem_iUnion.mp (hI hx)
    obtain ⟨hiI, hxi⟩ := Set.mem_iUnion.mp hi
    exact ⟨⟨i, hiI⟩, hxi⟩
  · intro i
    have hm : m i ≤ M := Finset.le_sup i.property
    have ht := ConcreteCategory.congr_hom
      (subdivisionAmbientSectionMap_transition X n (V i) (m i) (M - m i)) (z i)
    change (subdivisionAmbientSectionMap X n (V i) (m i + (M - m i))).hom
        ((rationalSubdivisionIterate X (M - m i)).f n (z i)) =
      (subdivisionAmbientSectionMap X n (V i) (m i)).hom (z i) at ht
    rw [Nat.add_sub_of_le hm] at ht
    exact ht.trans (hz i)

#print axioms subdivisionLimitSheaf_compact_common_stage
/-- Near a compact support, common-stage ambient representatives can be chosen on a finite cover with smaller patches whose closures remain in their domains.
Source: Bredon, Sheaf Theory, second edition, II.9 and VI.12; compact shrinkings for supported chains.
HC no distance; AV milestone no distance.
-/
theorem subdivisionLimitSheaf_compact_shrunk_representatives (X : TopCat.{0})
    [CompactSpace X] [T2Space X] (n : ℕ) (K : Set X) (hK : IsCompact K)
    (U : Opens X) (hKU : K ⊆ U)
    (s : ((subdivisionLimitSheafComplex X).X n).obj.obj (Opposite.op U)) :
    ∃ (I : Finset K) (V W : I → Opens X) (hV : ∀ i, V i ≤ U)
      (M : ℕ) (z : I → (SingularChainComplex ℚ X).X n),
      (∀ x ∈ K, ∃ i, x ∈ W i) ∧ (∀ i, closure (W i : Set X) ⊆ V i) ∧ ∀ i,
        (subdivisionAmbientSectionMap X n (V i) M).hom (z i) =
          ((subdivisionLimitSheafComplex X).X n).obj.map (homOfLE (hV i)).op s := by
  obtain ⟨I, V, hV, M, z, hcover, hz⟩ :=
    subdivisionLimitSheaf_compact_common_stage X n K hK U hKU s
  obtain ⟨W, hWcover, hcl⟩ := compact_open_patch_shrinking K hK V
    (fun x hx => Set.mem_iUnion.mpr (hcover x hx))
  refine ⟨I, V, W, hV, M, z, ?_, hcl, hz⟩
  intro x hx
  exact Set.mem_iUnion.mp (hWcover hx)

#print axioms subdivisionLimitSheaf_compact_shrunk_representatives
end HodgeLean.Foundations.RationalHomologyManifold
