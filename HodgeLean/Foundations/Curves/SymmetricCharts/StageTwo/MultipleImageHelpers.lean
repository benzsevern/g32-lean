import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.MultisetInsertionHelpers
import HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo.ClosedSupportHelpers
import HodgeLean.Foundations.Program.SchoenTowerL1bDivisorIncidenceSupport
import HodgeLean.Foundations.Program.SchoenCycleBranchImagePoints

/-! # The actual image of multiple point insertion

HC no distance; AV milestone no distance.
-/
noncomputable section
open CategoryTheory AlgebraicGeometry
open HodgeLean.Adapters HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000

/-- Branch support on a rational ordered tuple detects membership of the marked rational point.
Source: Schoen (1988), Lemma 2.2; effective-divisor incidence.
HC no distance; AV milestone no distance.
-/
theorem branch_support_coordinate_multiset
    (C B : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (hdim : TopologicalSpace.dim C.left = 1) (h : ℕ)
    (γ : g3_power C (h+1) ⟶ B) [IsFinite γ.left]
    (hsurj : Function.Surjective (Point.map γ))
    (hinv : ∀ σ, s2_permute C (h+1) σ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (h+1) ⟶ T),
      (∀ σ, s2_permute C (h+1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (p : ComplexPoint (g3_power C (h+1))) (b : ComplexPoint C) :
    (Point.map γ p).underlying ∈ (s2c_branchIdeal C B h γ b).support ↔
      b ∈ (List.ofFn (fun i => Point.map (g3_proj C (h+1) i) p) : Multiset (ComplexPoint C)) := by
  rw [Point.underlying_map, s2v_l1b_divisor_incidence_support_coordinate C B hdim h γ hsurj hinv huniv]
  constructor
  · rintro ⟨i, hi⟩
    apply List.mem_ofFn.mpr
    refine ⟨i, ?_⟩
    apply ComplexPoint.underlying_injective_of_locallyOfFiniteType
    exact hi
  · intro hb
    obtain ⟨i, hi⟩ := List.mem_ofFn.mp hb
    exact ⟨i, congrArg (fun q : ComplexPoint C => q.underlying) hi⟩

/-- The multiple-insertion immersion has exactly the support of the sum of the distinct branch ideals.
Source: Milne, Jacobian Varieties, §3; Schoen (1988), Lemma 2.2.
HC no distance; AV milestone no distance.
-/
theorem multiple_addition_range
    (C P B : Over (Spec ↧ℂ)) [IsIntegral C.left] [Smooth C.hom] [IsProjective C.hom]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom] [LocallyOfFiniteType P.hom]
    (hdim : TopologicalSpace.dim C.left = 1) (h k : ℕ) (hk : k ≤ h+1)
    (b : Fin k → ComplexPoint C) (hb : Function.Injective b)
    (π : g3_power C (h+1-k) ⟶ P) [Surjective π.left]
    (γ : g3_power C (h+1) ⟶ B) [IsFinite γ.left] [Surjective γ.left]
    (hinv : ∀ σ, s2_permute C (h+1) σ ≫ γ = γ)
    (huniv : ∀ (T : Over (Spec ↧ℂ)) (f : g3_power C (h+1) ⟶ T),
      (∀ σ, s2_permute C (h+1) σ ≫ f = f) → ∃! d : B ⟶ T, γ ≫ d = f)
    (a : P ⟶ B) [IsClosedImmersion a.left]
    (ha : π ≫ a = multipleInsertion C h k hk b ≫ γ) :
    Set.range a.left = ((⨆ i, s2c_branchIdeal C B h γ (b i)).support : Set B.left) := by
  classical
  let I := ⨆ i, s2c_branchIdeal C B h γ (b i)
  have hγpoint : Function.Surjective (Point.map γ) := by
    intro w
    exact s2e_complexPoint_lift_of_mem_range γ w (γ.left.surjective w.underlying)
  have hbranches (w : ComplexPoint B) : w.underlying ∈ I.support ↔
      ∀ i, w.underlying ∈ (s2c_branchIdeal C B h γ (b i)).support := by
    simp only [I, Scheme.IdealSheafData.support_iSup, TopologicalSpace.Closeds.mem_iInf]
  have hpoint (w : ComplexPoint B) : w.underlying ∈ I.support ↔ w.underlying ∈ Set.range a.left := by
    constructor
    · intro hw
      obtain ⟨z, hz⟩ := hγpoint w
      let s : Multiset (ComplexPoint C) := List.ofFn (fun i => Point.map (g3_proj C (h+1) i) z)
      have hmem (i : Fin k) : b i ∈ s := by
        apply (branch_support_coordinate_multiset C B hdim h γ hγpoint hinv huniv z (b i)).mp
        rw [hz]
        exact (hbranches w).mp hw i
      obtain ⟨r, hrCard, hr⟩ := multiset_remove_distinct (h+1-k) k s
        (by simp only [s, Multiset.coe_card, List.length_ofFn]; omega) b hb hmem
      let sr : Sym (ComplexPoint C) (h+1-k) := ⟨r, hrCard⟩
      obtain ⟨rr, hrr⟩ := s2e_sym_exists_enumeration sr
      let p := s2_lift (h+1-k) rr
      let p' := Point.map (multipleInsertion C h k hk b) p
      have hrcoords : (List.ofFn (fun i => Point.map (g3_proj C (h+1-k) i) p) :
          Multiset (ComplexPoint C)) = r := by
        have hpcoord : (fun i => Point.map (g3_proj C (h+1-k) i) p) = rr := by
          funext i
          exact s2_check_lift_proj (h+1-k) rr i
        rw [hpcoord]
        exact hrr
      have H : (List.ofFn (fun i => Point.map (g3_proj C (h+1) i) p') :
          Multiset (ComplexPoint C)) = s := by
        rw [multipleInsertion_point_multiset C h k hk b p, hrcoords, ← hr]
      have Hq := s2e_quotient_tuple_multiset_eq (h+1) γ hinv
        (fun i => Point.map (g3_proj C (h+1) i) p')
        (fun i => Point.map (g3_proj C (h+1) i) z) H
      change s2_lift (h+1) (fun i => p' ≫ g3_proj C (h+1) i) ≫ γ =
        s2_lift (h+1) (fun i => z ≫ g3_proj C (h+1) i) ≫ γ at Hq
      rw [s2e_lift_coordinates, s2e_lift_coordinates] at Hq
      have Ha : Point.map a (Point.map π p) = w := by
        change (p ≫ π) ≫ a = w
        rw [Category.assoc, ha, ← Category.assoc]
        exact Hq.trans hz
      exact ⟨(Point.map π p).underlying, congrArg (fun q : ComplexPoint B => q.underlying) Ha⟩
    · intro hw
      obtain ⟨q, hq⟩ := s2e_complexPoint_lift_of_mem_range a w hw
      obtain ⟨p, hp⟩ := s2e_complexPoint_lift_of_mem_range π q (π.left.surjective q.underlying)
      let p' := Point.map (multipleInsertion C h k hk b) p
      have Hw : Point.map γ p' = w := by
        change (p ≫ multipleInsertion C h k hk b) ≫ γ = w
        rw [Category.assoc, ← ha, ← Category.assoc]
        change Point.map a (Point.map π p) = w
        rw [hp, hq]
      apply (hbranches w).mpr
      intro i
      rw [← Hw]
      apply (branch_support_coordinate_multiset C B hdim h γ hγpoint hinv huniv p' (b i)).mpr
      rw [multipleInsertion_point_multiset C h k hk b p]
      apply Multiset.mem_add.mpr
      exact Or.inl (List.mem_ofFn.mpr ⟨i, rfl⟩)
  let S : TopologicalSpace.Closeds B.left := ⟨Set.range a.left, a.left.isClosedMap.isClosed_range⟩
  apply Set.Subset.antisymm
  · exact closed_subset_of_complex_points B S I.support (fun p hp => (hpoint p).mpr hp)
  · exact closed_subset_of_complex_points B I.support S (fun p hp => (hpoint p).mp hp)

end HodgeLean.Foundations.Curves.SymmetricCharts.StageTwo
