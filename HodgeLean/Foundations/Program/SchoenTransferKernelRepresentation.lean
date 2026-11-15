import HodgeLean.Foundations.Program.SchoenTransferRetraction
import HodgeLean.Foundations.Program.SchoenTransferCorrespondence
import HodgeLean.Foundations.Program.SchoenTransferPairing

/-! Realization of linear maps by a specified Künneth bidegree. -/
noncomputable section
set_option maxHeartbeats 400000
set_option maxRecDepth 2000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint MonoidalCategory
open CategoryTheory.CartesianMonoidalCategory
open HodgeLean.RealDefs HodgeLean.Adapters
open scoped BigOperators
attribute [local irreducible] cupProductOf homPullback algebraicCycleClassSpan
namespace HodgeLean.Foundations.Program

theorem s4_corrAction_representation
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim B.left = g) (hk : k ≤ g)
    (I : HQ B (2 * g) ≃ₗ[ℚ] ℚ)
    (F : HQ B (2 * (g - k)) →ₗ[ℚ] HQ A (2 * k)) :
    ∃ ξ : HQ (A ⊗ B) (2 * (2 * k)),
      ∀ x, cfd_corrAction A B g I (2 * k) (g - k) k (by omega) ξ x = F x := by
  classical
  letI := (finiteBetti_abelian B).finite (2 * (g - k))
  let b := Module.finBasis ℚ (HQ B (2 * (g - k)))
  let htop : 2 * k + 2 * (g - k) = 2 * g := by omega
  let P := ((cupProductOf B).cup htop).compr₂ I.toLinearMap
  let E := LinearEquiv.ofBijective P
    (s4_cupPairing_bijective B g hdim (2 * k) (2 * (g - k)) htop I)
  let ξ := fun i : Fin (Module.finrank ℚ (HQ B (2 * (g - k)))) =>
    (cupProductOf (A ⊗ B)).cup (show 2 * k + 2 * k = 2 * (2 * k) by omega)
      (homPullback (fst A B) (2 * k) (F (b i)))
      (homPullback (snd A B) (2 * k) (E.symm (b.coord i)))
  refine ⟨∑ i, ξ i, fun x => ?_⟩
  rw [s4_corrAction_sum, LinearMap.sum_apply]
  calc
    ∑ i, (cfd_corrAction A B g I (2 * k) (g - k) k (by omega) (ξ i)) x =
        ∑ i, b.repr x i • F (b i) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [s4_corrAction_cross A B g k hdim hk I]
      have he := congrArg (fun z => z x) (E.apply_symm_apply (b.coord i))
      change I ((cupProductOf B).cup htop (E.symm (b.coord i)) x) = b.repr x i at he
      rw [he]
    _ = F (∑ i, b.repr x i • b i) := by
      simp only [map_sum, map_smul]
    _ = F x := congrArg F (b.sum_repr x)


/-- The hard Lefschetz inverse has a cohomological correspondence representative. -/
theorem s4_inverse_lefschetz_cohomological
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (g k : ℕ) (hdim : TopologicalSpace.dim A.left = g) (hk : 2 * k ≤ g)
    (I : HQ A (2 * g) ≃ₗ[ℚ] ℚ) (pol : HQ A 2)
    (hη : HodgeLean.Foundations.Symplectic.IsNondegenerate
      (polarizationVec (torusCohomology_cupProductOf A) pol)) :
    ∃ ξ : HQ (A ⊗ A) (2 * (2 * k)),
      ∀ x : HQ A (2 * k),
        cfd_corrAction A A g I (2 * k) (g - k) k (by omega) ξ
          (lefschetzPow A (cupProductOf A) pol (g - 2 * k) (by omega) x) = x := by
  let L := lefschetzPow A (cupProductOf A) pol (g - 2 * k)
    (show 2 * k + 2 * (g - 2 * k) = 2 * (g - k) by omega)
  have hL : Function.Bijective L := by
    have hh := (hardLefschetz_abelian A hη).bijective
      (k := 2 * k) (m := 2 * (g - k)) (by omega) (by omega)
    simpa only [hdim] using hh
  let E := LinearEquiv.ofBijective L hL
  obtain ⟨ξ, hξ⟩ := s4_corrAction_representation A A g k hdim (by omega) I
    E.symm.toLinearMap
  refine ⟨ξ, fun x => ?_⟩
  rw [hξ]
  exact E.symm_apply_apply x


/-- A stable space of algebraic correspondence operators supplies an algebraic retraction. -/
theorem s4_algebraic_correspondence_retraction
    (A : Over (Spec ↧ℂ)) [GrpObj A] [IsCommMonObj A]
    [IsIntegral A.left] [Smooth A.hom] [IsProjective A.hom]
    (B : Over (Spec ↧ℂ)) [GrpObj B] [IsCommMonObj B]
    [IsIntegral B.left] [Smooth B.hom] [IsProjective B.hom]
    (d : ℕ) (I : HQ B (2 * d) ≃ₗ[ℚ] ℚ) (c p q : ℕ)
    (h : 2 * c + 2 * p = 2 * q + 2 * d)
    (L : HQ A (2 * q) →ₗ[ℚ] HQ B (2 * p))
    (κ : HQ (A ⊗ B) (2 * c)) (hκ : κ ∈ cfd_cycleSpan (A ⊗ B) c) :
    let F := s4_corrActionLinear A B d I c p q h
    (∀ T ∈ (cfd_cycleSpan (A ⊗ B) c).map F,
      ((F κ).comp L).comp T ∈ (cfd_cycleSpan (A ⊗ B) c).map F) →
    Function.Injective ((F κ).comp L) →
    ∃ ξ : HQ (A ⊗ B) (2 * c), ξ ∈ cfd_cycleSpan (A ⊗ B) c ∧
      (cfd_corrAction A B d I c p q h ξ).comp L = LinearMap.id := by
  dsimp only
  intro hstable hinj
  letI := (finiteBetti_abelian A).finite (2 * q)
  letI := (finiteBetti_abelian B).finite (2 * p)
  let F := s4_corrActionLinear A B d I c p q h
  let U := (cfd_cycleSpan (A ⊗ B) c).map F
  have hκ' : F κ ∈ U := Submodule.mem_map.mpr ⟨κ, hκ, rfl⟩
  obtain ⟨T, hT, hTL⟩ := s4_retraction_in_stable_submodule U L (F κ)
    hκ' hstable hinj
  obtain ⟨ξ, hξ, hFξ⟩ := Submodule.mem_map.mp hT
  refine ⟨ξ, hξ, ?_⟩
  change (F ξ).comp L = LinearMap.id
  rw [hFξ]
  exact hTL

end HodgeLean.Foundations.Program
