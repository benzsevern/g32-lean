import HodgeLean.Foundations.Program.SchoenTowerPowerOpenImmersion
import HodgeLean.Foundations.Program.SchoenTowerPointRetractions
import HodgeConjecture.Lemmas.AlgebraicGeometry.ComplexPoint.Open

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint
open HodgeLean.Adapters HodgeLean.RealDefs
namespace HodgeLean.Foundations.Program

/-- Factor a morphism over the complex base through an open containing its image.
Source: Mathlib, IsOpenImmersion.lift. -/
def s2t_overOpenLift {T C : Over (Spec ↧ℂ)} (f : T ⟶ C) (U : C.left.Opens)
    (hf : Set.range f.left ⊆ U) : T ⟶ openScheme C U := by
  have hr : Set.range f.left ⊆ Set.range U.ι := by
    intro z hz
    exact ⟨⟨z, hf hz⟩, rfl⟩
  let l := IsOpenImmersion.lift U.ι f.left hr
  have hl : l ≫ U.ι = f.left := IsOpenImmersion.lift_fac _ _ _
  refine Over.homMk l ?_
  change l ≫ (U.ι ≫ C.hom) = T.hom
  rw [← Category.assoc, hl]
  exact Over.w f

@[reassoc]
theorem s2t_overOpenLift_fac {T C : Over (Spec ↧ℂ)} (f : T ⟶ C) (U : C.left.Opens)
    (hf : Set.range f.left ⊆ U) : s2t_overOpenLift f U hf ≫ openInclusion C U = f := by
  apply Over.OverMorphism.ext
  exact IsOpenImmersion.lift_fac _ _ _

/-- A retained open power consists precisely of tuples whose projections belong to that open.
Source: Mac Lane, Categories for the Working Mathematician, III.4; the product universal property. -/
theorem s2t_powerOpen_range (C : Over (Spec ↧ℂ)) (U : C.left.Opens) (n : ℕ) :
    Set.range (s2_powerMap (openInclusion C U) n).left =
      {x | ∀ i, (g3_proj C n i).left x ∈ U} := by
  apply Set.Subset.antisymm
  · rintro _ ⟨y, rfl⟩ i
    have he : s2_powerMap (openInclusion C U) n ≫ g3_proj C n i =
        g3_proj (openScheme C U) n i ≫ openInclusion C U := by
      simp only [s2_powerMap, s2_check_lift_proj]
    have hp := congrArg (fun f => f.left y) he
    simp only [Over.comp_left, Scheme.Hom.comp_apply] at hp
    change (g3_proj C n i).left ((s2_powerMap (openInclusion C U) n).left y) ∈ U
    rw [hp]
    exact ((g3_proj (openScheme C U) n i).left y).property
  · intro x hx
    let W : (g3_power C n).left.Opens := ⨅ i, (g3_proj C n i).left ⁻¹ᵁ U
    have hW (y : (g3_power C n).left) : y ∈ W ↔ ∀ i, (g3_proj C n i).left y ∈ U := by
      change y ∈ (W : Set (g3_power C n).left) ↔ _
      rw [TopologicalSpace.Opens.coe_iInf]
      simp only [Set.mem_iInter, SetLike.mem_coe, Scheme.Hom.mem_preimage]
    let T := openScheme (g3_power C n) W
    let t := openInclusion (g3_power C n) W
    have hr (i : Fin n) : Set.range (t ≫ g3_proj C n i).left ⊆ U := by
      rintro _ ⟨y, rfl⟩
      exact ((hW y.val).mp y.property) i
    let l : T ⟶ g3_power (openScheme C U) n :=
      s2_lift n (fun i => s2t_overOpenLift (t ≫ g3_proj C n i) U (hr i))
    have hfac : l ≫ s2_powerMap (openInclusion C U) n = t := by
      apply s2_product_hom_ext n
      intro i
      simp only [Category.assoc, s2_powerMap, s2_check_lift_proj]
      rw [← Category.assoc]
      change (s2_lift n _ ≫ g3_proj (openScheme C U) n i) ≫ openInclusion C U = _
      rw [s2_check_lift_proj, s2t_overOpenLift_fac]
    refine ⟨l.left ⟨x, (hW x).mpr hx⟩, ?_⟩
    exact congrArg (fun f : T ⟶ g3_power C n => f.left ⟨x, (hW x).mpr hx⟩) hfac

/-- Point insertion commutes with the actual finite-power map. -/
theorem s2t_branchInsertion_powerMap {C D : Over (Spec ↧ℂ)} (f : C ⟶ D)
    (n : ℕ) (b : ComplexPoint C) :
    s2c_branchInsertion C n b ≫ s2_powerMap f (n + 1) =
      s2_powerMap f n ≫ s2c_branchInsertion D n (b ≫ f) := by
  apply s2_product_hom_ext (n + 1)
  intro k
  refine Fin.cases ?_ (fun i => ?_) k
  · simp only [Category.assoc, s2_powerMap, s2c_branchInsertion, s2_check_lift_proj,
      Fin.cases_zero, s2t_comp_toUnit_assoc]
    rw [← Category.assoc, s2_check_lift_proj]
    rfl
  · simp only [Category.assoc, s2_powerMap, s2c_branchInsertion, s2_check_lift_proj, Fin.cases_succ]
    rw [← Category.assoc, s2_check_lift_proj]
    rfl

/-- Insertion of a point already in an open pulls its open power back to the previous open power. -/
theorem s2t_branchInsertion_preimage_powerOpen (C : Over (Spec ↧ℂ)) (U : C.left.Opens)
    (n : ℕ) (b : ComplexPoint (openScheme C U)) :
    (s2c_branchInsertion C n (b ≫ openInclusion C U)).left ⁻¹'
        Set.range (s2_powerMap (openInclusion C U) (n + 1)).left =
      Set.range (s2_powerMap (openInclusion C U) n).left := by
  rw [s2t_powerOpen_range, s2t_powerOpen_range]
  ext x
  change (∀ i, (g3_proj C (n + 1) i).left
    ((s2c_branchInsertion C n (b ≫ openInclusion C U)).left x) ∈ U) ↔ _
  let v : Fin (n + 1) → (g3_power C n ⟶ C) :=
    Fin.cases (CartesianMonoidalCategory.toUnit (g3_power C n) ≫ (b ≫ openInclusion C U))
      (fun j => g3_proj C n j)
  have hp (i : Fin (n + 1)) :
      (g3_proj C (n + 1) i).left ((s2c_branchInsertion C n (b ≫ openInclusion C U)).left x) =
      (v i).left x := congrArg (fun f : g3_power C n ⟶ C => f.left x)
        (s2_check_lift_proj (n + 1) v i)
  simp only [hp]
  constructor
  · intro h i
    exact h i.succ
  · intro h i
    refine Fin.cases ?_ (fun j => h j) i
    exact (b.left ((CartesianMonoidalCategory.toUnit (g3_power C n)).left x)).property

example {T C : Over (Spec ↧ℂ)} (f : T ⟶ C) (U : C.left.Opens)
    (hf : Set.range f.left ⊆ U) : s2t_overOpenLift f U hf ≫ openInclusion C U = f :=
  s2t_overOpenLift_fac f U hf

end HodgeLean.Foundations.Program
