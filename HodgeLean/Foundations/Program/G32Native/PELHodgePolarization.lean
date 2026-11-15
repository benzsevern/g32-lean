import HodgeLean.Foundations.PositivePolarization
import HodgeLean.Foundations.Program.G32Native.PELHodgeTensorContainment

noncomputable section
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open scoped CategoryTheory.MonObj TensorProduct
open HodgeLean.RealDefs HodgeLean.Adapters HodgeLean.Foundations
namespace HodgeLean.Foundations.Program.GeneralTypeIII
variable (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
  [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
local instance : Module.Finite ℚ (HQ A 1) := (torusCohomology_cupProductOf A).finite
variable (pol : HQ A 2)
  (hη : Symplectic.IsNondegenerate (polarizationVec (torusCohomology_cupProductOf A) pol))
  (hpos : PolarizationPositive (finiteBetti_abelian A) (spec_bettiDeRhamIso_abelian A)
    (hodgeDecomposition_of_abelian A) (torusCohomology_cupProductOf A) hη)

include hpos

/-- The geometric polarization pairs only opposite Hodge-circle weights.
Source: Birkenhake–Lange, Complex Abelian Varieties, second edition, §4.2;
Abdulali, Annals of Mathematics 155 (2002), §2.1. -/
theorem polarization_weight_orthogonality
    (p q r s : ℤ) (x : ℂ ⊗[ℚ] HQ A 1) (hx : x ∈ cohomologyHodgePiece A 1 (p, q))
    (y : ℂ ⊗[ℚ] HQ A 1) (hy : y ∈ cohomologyHodgePiece A 1 (r, s))
    (hne : p - q + (r - s) ≠ 0) :
    (polarizationForm (torusCohomology_cupProductOf A) hη).baseChange ℂ x y = 0 := by
  have hP := (p1_isPolarization_iff A pol).2 ⟨hη, hpos⟩
  obtain ⟨⟨h10, h01⟩, -⟩ := (spec_firstRiemannRelation A (finiteBetti_abelian A)
    (spec_bettiDeRhamIso_abelian A) hη).1 (p1_mem_hdg A hP)
  by_cases hx10 : (p, q) = (1, 0)
  · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx10
    by_cases hy10 : (r, s) = (1, 0)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy10
      exact h10 x hx y hy
    · by_cases hy01 : (r, s) = (0, 1)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy01
        norm_num at hne
      · rw [spec_g4_cohomologyHodgePiece_one_eq, latticeHodgePieces,
          if_neg hy10, if_neg hy01, Submodule.mem_bot] at hy
        subst y
        exact map_zero _
  · by_cases hx01 : (p, q) = (0, 1)
    · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx01
      by_cases hy01 : (r, s) = (0, 1)
      · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy01
        exact h01 x hx y hy
      · by_cases hy10 : (r, s) = (1, 0)
        · obtain ⟨rfl, rfl⟩ := Prod.mk.inj hy10
          norm_num at hne
        · rw [spec_g4_cohomologyHodgePiece_one_eq, latticeHodgePieces,
            if_neg hy10, if_neg hy01, Submodule.mem_bot] at hy
          subst y
          exact map_zero _
    · rw [spec_g4_cohomologyHodgePiece_one_eq, latticeHodgePieces,
        if_neg hx10, if_neg hx01, Submodule.mem_bot] at hx
      subst x
      simp only [map_zero, LinearMap.zero_apply]

/-- Every polarized abelian variety's Hodge group centralizes its retained
endomorphisms and preserves its polarization, in the identity component.
Source: Abdulali, Annals of Mathematics 155 (2002), §§2.1, 3.2. -/
theorem polarized_hodgeGroup_subset_connected_pel
    {I : Type*} (ops : I → AbelianEnd0 A)
    {n : ℕ} (basis : Module.Basis (Fin n) ℚ (HQ A 1)) :
    g2_hodgeGroup (latticeHodgePieces A) (spec_latticeHodgePieces_isInternal A) basis ⊆
      pelGenericGroup
        ((LinearMap.toMatrix₂ basis basis
          (polarizationForm (torusCohomology_cupProductOf A) hη)).map (algebraMap ℚ ℂ))
        (Set.range fun i =>
          (LinearMap.toMatrix basis basis (abelianEnd0Action A (ops i)).unop).map
            (algebraMap ℚ ℂ)) := by
  let E := polarizationForm (torusCohomology_cupProductOf A) hη
  let Ts := fun i => (abelianEnd0Action A (ops i)).unop
  have he : ∀ p q r s : ℤ, ∀ x ∈ latticeHodgePieces A (p, q),
      ∀ y ∈ latticeHodgePieces A (r, s), p - q + (r - s) ≠ 0 →
        E.baseChange ℂ x y = 0 := by
    intro p q r s x hx y hy hn
    apply polarization_weight_orthogonality A pol hη hpos p q r s x _ y _ hn
    · rwa [spec_g4_cohomologyHodgePiece_one_eq]
    · rwa [spec_g4_cohomologyHodgePiece_one_eq]
  have hr : ∀ T ∈ Set.range Ts, ∀ pq x, x ∈ latticeHodgePieces A pq →
      T.baseChange ℂ x ∈ latticeHodgePieces A pq := by
    rintro _ ⟨i, rfl⟩ pq x hx
    have hm := p1r_map_cohomologyHodgePiece_le A
      (spec_g4_abelianEnd0Action_mem_hodgeEndH1 A (ops i)) pq
    rw [spec_g4_cohomologyHodgePiece_one_eq] at hm
    exact hm (Submodule.mem_map_of_mem hx)
  have hu := hodgeGroup_subset_pel_of_tensors (latticeHodgePieces A)
    (spec_latticeHodgePieces_isInternal A) basis E (Set.range Ts) he hr
  simpa only [Ts, E, ← Set.range_comp, Function.comp_def] using hu

#print axioms polarized_hodgeGroup_subset_connected_pel
#print axioms polarization_weight_orthogonality
end HodgeLean.Foundations.Program.GeneralTypeIII
