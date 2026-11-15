import HodgeLean.Foundations.Program.PrymVariationCentrePolynomial
import HodgeLean.Foundations.Program.PrymVariation
import HodgeLean.Foundations.Program.PrymFamilyB4Proofs
import HodgeLean.Papers.G32Family

noncomputable section
open CategoryTheory AlgebraicTopology.Singular HodgeLean.Papers
open scoped Manifold ContDiff TensorProduct
namespace HodgeLean.Foundations.Program
attribute [local instance] b4cov_sphChartedSpace b4cov_sph_isManifold

theorem b63d_invariantForms_eq_bot (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
    [FaithfulSMul b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (p : C → OnePoint ℂ)
    (hp : ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω p)
    (hs : Function.Surjective p)
    (hgal : b4_IsGaloisCover b4b_Group p) :
    b4_invariantForms ℂ C b4b_Group = ⊥ := by
  letI : Nonempty C := ⟨Classical.choose (hs default)⟩
  letI : FiniteDimensional ℂ (b3_HolForm ℂ C) :=
    b3_holForm_finiteDimensional (C := C) (by simp)
  letI : FiniteDimensional ℂ (b4_invariantForms ℂ C b4b_Group) :=
    Submodule.finiteDimensional_of_le inf_le_left
  have hfin : Module.finrank ℂ (b4_invariantForms ℂ C b4b_Group) = 0 := by
    calc
      Module.finrank ℂ (b4_invariantForms ℂ C b4b_Group) =
          Module.finrank ℂ (b3_HolForm ℂ (OnePoint ℂ)) := by
            exact b4_invariantForms_galois (by simp) (by simp) hG p hp hgal
      _ = 0 := b4b_sphere_genus
  exact Submodule.finrank_eq_zero.mp hfin

noncomputable def b63d_rotationGenerator (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
    [FaithfulSMul b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (x : C) : b4b_Group :=
  Classical.choose (b4_exists_rotGen (by simp) hG x)

theorem b63d_rotationGenerator_isRotGen (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
    [FaithfulSMul b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (x : C) : b4_IsRotGen ℂ x (b63d_rotationGenerator C hG x) :=
  Classical.choose_spec (b4_exists_rotGen (by simp) hG x)

theorem b63d_rotationGenerator_eq (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
    [FaithfulSMul b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (x : C) (g : b4b_Group) (hg : b4_IsRotGen ℂ x g) :
    b63d_rotationGenerator C hG x = g := by
  exact b4_rotGen_unique (by simp) hG x _ _
    (b63d_rotationGenerator_isRotGen C hG x) hg

theorem b63d_rotationGenerator_at_branches (C : Type) [TopologicalSpace C]
    [ChartedSpace ℂ C] [IsManifold 𝓘(ℂ, ℂ) ω C] [T2Space C]
    [CompactSpace C] [ConnectedSpace C] [MulAction b4b_Group C]
    [FaithfulSMul b4b_Group C]
    (hG : ∀ g : b4b_Group, ContMDiff 𝓘(ℂ, ℂ) 𝓘(ℂ, ℂ) ω (fun x : C ↦ g • x))
    (p : C → OnePoint ℂ) (q : Fin 13 → OnePoint ℂ)
    (hrot : ∀ i : Fin 13, ∃ x : C, p x = q i ∧ b4_IsRotGen ℂ x (b4b_root i)) :
    ∃ x : Fin 13 → C, (∀ i, p (x i) = q i) ∧
      ∀ i, b63d_rotationGenerator C hG (x i) = b4b_root i := by
  choose x hpx hx using hrot
  refine ⟨x, hpx, fun i ↦ ?_⟩
  exact b63d_rotationGenerator_eq C hG (x i) (b4b_root i) (hx i)

def b63d_rootClassPerm : Equiv.Perm (Fin 13) :=
  Equiv.ofBijective ![0, 6, 1, 7, 2, 8, 3, 9, 4, 10, 5, 11, 12] (by decide)

theorem b63d_root_classes (j : Fin 13) :
    g32h_ConjIn (g32h_classRep g32h_omega (b63d_rootClassPerm j))
      (b4b_toMatrix (b4b_root j)) := by
  fin_cases j
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_positiveSlot] using b63_root_positive_class 0
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_negativeSlot] using b63_root_negative_class 0
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_positiveSlot] using b63_root_positive_class 1
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_negativeSlot] using b63_root_negative_class 1
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_positiveSlot] using b63_root_positive_class 2
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_negativeSlot] using b63_root_negative_class 2
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_positiveSlot] using b63_root_positive_class 3
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_negativeSlot] using b63_root_negative_class 3
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_positiveSlot] using b63_root_positive_class 4
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_negativeSlot] using b63_root_negative_class 4
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_positiveSlot] using b63_root_positive_class 5
  · simpa [b63d_rootClassPerm, g32h_classRep, b63_negativeSlot] using b63_root_negative_class 5
  · exact ⟨1, one_mem _, 1, one_mem _, by simp, by
      simp [b63d_rootClassPerm, g32h_classRep, b4b_root, b4b_generators, b4b_toMatrix, pow_two]⟩

theorem b63d_root_product : (List.ofFn b4b_root).prod = 1 := by
  rw [show List.ofFn b4b_root =
      (List.ofFn b4b_root).take 8 ++
        ((List.ofFn b4b_root).drop 8).take 4 ++ [b4b_root 12] by rfl]
  rw [List.prod_append, List.prod_append, b63_root_prefix_product,
    b63_root_tail_product]
  change 1 * (b4b_generators 2) ^ 2 * ((b4b_generators 2) ^ 2 * 1) = 1
  rw [one_mul, mul_one, ← pow_add, b63_generator_two_fourth]

theorem b63d_root_subgroup : Subgroup.closure (Set.range b4b_root) = ⊤ := by
  apply top_unique
  intro g hg
  let H := Subgroup.closure (Set.range b4b_root)
  change g ∈ H
  have hind : ∀ (x : Matrix (Fin 4) (Fin 4) ℂ), x ∈ Submonoid.closure
        {g32R1 g32h_omega, g32R2 g32h_omega, g32X g32h_omega, g32Y g32h_omega} →
      ∃ hx : x ∈ g32h_G, (⟨x, hx⟩ : b4b_Group) ∈ H := by
    intro x hcl
    induction hcl using Submonoid.closure_induction with
    | mem x hmem =>
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
        rcases hmem with rfl | rfl | rfl | rfl
        · exact ⟨(b4b_generators 0).property, b63_root_generators 0⟩
        · exact ⟨(b4b_generators 1).property, b63_root_generators 1⟩
        · exact ⟨(b4b_generators 2).property, b63_root_generators 2⟩
        · exact ⟨(b4b_generators 3).property, b63_root_generators 3⟩
    | one => exact ⟨one_mem _, one_mem H⟩
    | mul x y hx hy ihx ihy =>
        rcases ihx with ⟨hxG, hxH⟩
        rcases ihy with ⟨hyG, hyH⟩
        exact ⟨mul_mem hxG hyG, H.mul_mem hxH hyH⟩
  rcases hind g.val g.property with ⟨hgG, hmem⟩
  simpa using hmem

theorem b63d_root_matrix_closure :
    Submonoid.closure (Set.range (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i))) = g32h_G := by
  let M := Submonoid.closure (Set.range (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)))
  have hr (i : Fin 13) : b4b_toMatrix (b4b_root i) ∈ M :=
    Submonoid.subset_closure ⟨i, rfl⟩
  apply le_antisymm
  · apply Submonoid.closure_le.mpr
    rintro x ⟨i, rfl⟩
    exact (b4b_root i).property
  · apply Submonoid.closure_le.mpr
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · change b4b_toMatrix (b4b_generators 0) ∈ M
      change b4b_toMatrix (b4b_root 0) ∈ M
      exact hr 0
    · change b4b_toMatrix (b4b_generators 1) ∈ M
      change b4b_toMatrix (b4b_root 3) ∈ M
      exact hr 3
    · change b4b_toMatrix (b4b_generators 2) ∈ M
      rw [← b63_generator_two_root_word_eq]
      change b4b_toMatrix (b4b_root 0 * b4b_root 4 * b4b_root 7 * b4b_root 8 *
        b4b_root 3 * b4b_root 12 * b4b_root 2 * b4b_root 6) ∈ M
      simp only [map_mul]
      exact M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem
        (M.mul_mem (M.mul_mem (hr 0) (hr 4)) (hr 7)) (hr 8)) (hr 3)) (hr 12)) (hr 2)) (hr 6)
    · change b4b_toMatrix (b4b_generators 3) ∈ M
      rw [← b63_generator_three_root_word_eq]
      change b4b_toMatrix (b4b_root 0 * b4b_root 2 * b4b_root 11 * b4b_root 2 *
        b4b_root 12 * b4b_root 6) ∈ M
      simp only [map_mul]
      exact M.mul_mem (M.mul_mem (M.mul_mem (M.mul_mem
        (M.mul_mem (hr 0) (hr 2)) (hr 11)) (hr 2)) (hr 12)) (hr 6)

theorem b63d_root_nielsen :
    g32h_Nielsen (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) := by
  refine ⟨⟨b63d_rootClassPerm, b63d_root_classes⟩, ?_, b63d_root_matrix_closure⟩
  change (List.ofFn (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i))).prod = 1
  calc
    _ = ((List.ofFn b4b_root).map b4b_toMatrix).prod := by rfl
    _ = b4b_toMatrix (List.ofFn b4b_root).prod :=
      (map_list_prod b4b_toMatrix (List.ofFn b4b_root)).symm
    _ = 1 := by rw [b63d_root_product, map_one]

theorem b63d_root_multCW :
    g32h_multCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) = 6 :=
  g32h_multCW_of_nielsen _ b63d_root_nielsen

theorem b63d_root_holoCW :
    g32h_holoCW (fun i : Fin 13 ↦ b4b_toMatrix (b4b_root i)) = 3 :=
  g32h_holoCW_of_nielsen _ b63d_root_nielsen

end HodgeLean.Foundations.Program
