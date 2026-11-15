import HodgeLean.Foundations.Program.SchoenTowerL1bKummerSections
import Mathlib.RingTheory.RootsOfUnity.Complex

noncomputable section
set_option maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Complex constants supply primitive roots of every positive order in the actual base function field. -/
theorem s2v_l1b_functionField_primitiveRoots
    (B : Over (Spec (CommRingCat.of ℂ))) [IsIntegral B.left]
    (n : ℕ) (hn : 0 < n) : (primitiveRoots n B.left.functionField).Nonempty := by
  haveI : Nonempty (⊤ : B.left.Opens) := ⟨⟨Classical.arbitrary B.left, trivial⟩⟩
  let κ : CommRingCat.of ℂ ⟶ B.left.functionField :=
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ B.hom.appTop ≫
      B.left.germToFunctionField ⊤
  refine ⟨κ (Complex.exp (2 * Real.pi * Complex.I / n)), ?_⟩
  apply (mem_primitiveRoots hn).mpr
  exact (Complex.isPrimitiveRoot_exp n (Nat.ne_of_gt hn)).map_of_injective κ.hom.injective

/-- For a complex base, cyclic generation along the actual section map needs no extra root data. -/
theorem s2v_l1b_complex_generic_cyclic_section_generator
    {K : Type} [Field K]
    (B : Over (Spec (CommRingCat.of ℂ))) [IsIntegral B.left]
    [Algebra B.left.functionField K] [FiniteDimensional B.left.functionField K]
    [IsGalois B.left.functionField K] [IsCyclic (K ≃ₐ[B.left.functionField] K)]
    (η : Spec (.of K) ⟶ B.left)
    (hη : Spec.map (CommRingCat.ofHom (algebraMap B.left.functionField K)) ≫
      B.left.fromSpecStalk (genericPoint B.left) = η)
    (U : B.left.affineOpens) [Nonempty U.1]
    (hU : ⊤ ≤ (B.left.fromSpecStalk (genericPoint B.left)) ⁻¹ᵁ U.1)
    (hηU : ⊤ ≤ η ⁻¹ᵁ U.1) :
    let ρ := (η.appLE U.1 ⊤ hηU ≫ (Scheme.ΓSpecIso (.of K)).hom).hom
    ∃ t : K, t ≠ 0 ∧ Subfield.closure (Set.range ρ ∪ {t}) = ⊤ ∧
      t ^ Module.finrank B.left.functionField K ∈
        Set.range (algebraMap B.left.functionField K) := by
  exact s2v_l1b_generic_cyclic_section_generator B.left η hη U hU hηU
    (s2v_l1b_functionField_primitiveRoots B _ Module.finrank_pos)

end HodgeLean.Foundations.Program
