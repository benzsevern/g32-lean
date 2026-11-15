import HodgeLean.Foundations.AlgebraicGeometry.SingularCycles.EtaleAffineOpenEvaluation

/-! # Holomorphic regular evaluations along local étale sections

HC no distance; AV milestone no distance.
-/

noncomputable section
open scoped Classical
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open Set Filter Topology HodgeLean.Foundations.Analytic
namespace AlgebraicGeometry.SingularCycles

/-- Continuous local sections of étale maps pull regular evaluations back to holomorphic functions.
Source: SGA 1, Exposé XII, §1; affine étale neighbourhoods and regular evaluation. -/
theorem etale_section_regular_evaluation {X Z : Over (Spec ↧ℂ)}
    [LocallyOfFiniteType X.hom] [QuasiCompact X.hom] [IsSeparated X.hom]
    [LocallyOfFiniteType Z.hom] [QuasiCompact Z.hom] [IsSeparated Z.hom]
    (f : X ⟶ Z) [Etale f.left] {U : Set (ComplexPoint Z)} (hU : IsOpen U)
    (s : U → ComplexPoint X) (hs : Continuous s)
    (hsection : ∀ y, Point.map f (s y) = (y : ComplexPoint Z))
    (O : X.left.Opens) (hsO : ∀ y, (s y).underlying ∈ O) (b : Γ(X.left, O)) :
    (f4_analytification Z).IsHolFun (fun y => Point.evaluate O b (s y)) := by
  apply holFun_of_local (f4_analytification Z)
  intro y
  obtain ⟨A, hA, hyA, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := Z.left) (x := (y : ComplexPoint Z).underlying) (U := ⊤) trivial
  have hsy : (s y).underlying ∈ O ⊓ f.left ⁻¹ᵁ A := by
    refine ⟨hsO y, ?_⟩
    change (Point.map f (s y)).underlying ∈ A
    rw [hsection]
    exact hyA
  obtain ⟨B, hB, hyB, hBOA⟩ := exists_isAffineOpen_mem_and_subset hsy
  have hBA : B ≤ f.left ⁻¹ᵁ A := hBOA.trans inf_le_right
  have hBO : B ≤ O := hBOA.trans inf_le_left
  let W : Set U := {z | s z ∈ Point.overOpen B}
  let V : Set (ComplexPoint Z) := Subtype.val '' W
  have hVU : V ⊆ U := fun z ⟨z', _, heq⟩ => heq ▸ z'.2
  have hVo : IsOpen V := hU.isOpenMap_subtype_val W ((Point.isOpen_overOpen B).preimage hs)
  have hyV : (y : ComplexPoint Z) ∈ V := ⟨y, hyB, rfl⟩
  refine ⟨V, hVU, hVo, hyV, ?_⟩
  let sV : V → ComplexPoint X := fun z => s ⟨z, hVU z.2⟩
  have hsV : Continuous sV := hs.comp (continuous_subtype_val.subtype_mk fun z => hVU z.2)
  have hsVB : ∀ z : V, (sV z).underlying ∈ B := by
    intro z
    obtain ⟨z', hz', heq⟩ := z.2
    have hzz : (⟨z, hVU z.2⟩ : U) = z' := Subtype.ext heq.symm
    change (s ⟨z, hVU z.2⟩).underlying ∈ B
    rw [hzz]
    exact hz'
  have hVA : V ⊆ Point.overOpen A := by
    intro z hz
    have hf : Point.map f (sV ⟨z, hz⟩) = z := hsection ⟨z, hVU hz⟩
    change z.underlying ∈ A
    rw [← hf]
    exact hBA (hsVB ⟨z, hz⟩)
  have hbase : ∀ a : Γ(Z.left, A), (f4_analytification Z).IsHolFun
      (fun z : V => Point.evaluate A a (Point.map f (sV z))) := by
    intro a
    have heq : (fun z : V => Point.evaluate A a (Point.map f (sV z))) =
        (fun z : V => Point.evaluate A a z) := by
      funext z
      exact congrArg (Point.evaluate A a) (hsection ⟨z, hVU z.2⟩)
    rw [heq]
    exact anb_isHolFun_restrict _ hVA (f4_isHolFun_evaluate Z A a)
  let bB : Γ(X.left, B) := X.left.presheaf.map (homOfLE hBO).op b
  have h := etale_affineOpen_lift_evaluation (f4_analytification Z) hVo f A hA B hB
    hBA sV hsV hsVB hbase bB
  have heq : (fun z : V => Point.evaluate O b (sV z)) =
      (fun z : V => Point.evaluate B bB (sV z)) := by
    funext z
    exact Point.evaluate_res hBO b (sV z) (hsVB z)
  change (f4_analytification Z).IsHolFun (fun z : V => Point.evaluate O b (sV z))
  rw [heq]
  exact h

end AlgebraicGeometry.SingularCycles
