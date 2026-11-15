module

public import HodgeLean.Foundations.Program.SchoenExceptionalNaturality
public import HodgeLean.Foundations.Program.SchoenExceptionalFibreAcyclic
public import Mathlib.Topology.Sheaves.LocallySurjective

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] TopCat.Sheaf.extAddCommGroup

set_option backward.isDefEq.respectTransparency false in
theorem s3_sections_surjective_of_H_one {T : TopCat.{0}}
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} T)} (hS : S.ShortExact)
    (hF : Subsingleton (CategoryTheory.Sheaf.H S.X₁ 1)) :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  let : Subsingleton (Abelian.Ext 𝓒(T; ULift ℤ) S.X₁ 1) := hF
  intro c
  let x : Abelian.Ext 𝓒(T; ULift ℤ) S.X₃ 0 := (s3_globalSectionsEquiv S.X₃).symm c
  have hx : x.comp hS.extClass (by decide : 0 + 1 = 1) = 0 := Subsingleton.elim _ _
  obtain ⟨b, hb⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hS x rfl hx
  refine ⟨s3_globalSectionsEquiv S.X₂ b, ?_⟩
  rw [s3_globalSectionsEquiv_naturality, hb]
  exact (s3_globalSectionsEquiv S.X₃).apply_symm_apply c

set_option backward.defeqAttrib.useBackward true in
set_option backward.isDefEq.respectTransparency false in
theorem s3_proper_pushforward_epi {X Y : TopCat.{0}} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (hF : ∀ y : Y, Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).obj S.X₁) 1)) :
    Epi ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).map S.g) := by
  apply (TopCat.Sheaf.isLocallySurjective_iff_epi _).mp
  apply (TopCat.Presheaf.locally_surjective_iff_surjective_on_stalks _).mpr
  intro y c
  let R := S.map (TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y))
  have hR : R.ShortExact := s3_pullback_shortExact _ hS
  obtain ⟨b, hb⟩ := s3_sections_surjective_of_H_one hR (hF y)
    (s3_proper_stalk_to_sections p S.X₃ y c)
  obtain ⟨a, ha⟩ := (s3_proper_stalk_to_sections_bijective p hp S.X₂ y).2 b
  refine ⟨a, ?_⟩
  apply (s3_proper_stalk_to_sections_bijective p hp S.X₃ y).1
  calc
    _ = R.g.hom.app (op ⊤) (s3_proper_stalk_to_sections p S.X₂ y a) :=
      congrArg (fun f => f a) (s3_proper_stalk_to_sections_naturality p S.g y)
    _ = _ := by rw [ha, hb]

theorem s3_proper_pushforward_shortExact {X Y : TopCat.{0}} [T2Space X] [LocallyCompactSpace X]
    (p : X ⟶ Y) (hp : IsProperMap p)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)} (hS : S.ShortExact)
    (hF : ∀ y : Y, Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).obj S.X₁) 1)) :
    (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p)).ShortExact := by
  let P := TopCat.Sheaf.pushforward AddCommGrpCat.{0} p
  letI : P.Additive := Functor.additive_of_preserves_binary_products P
  have hleft := (((Functor.preservesFiniteLimits_tfae P).out 2 4 rfl rfl).mpr
    inferInstance) S ⟨hS.exact, hS.mono_f⟩
  exact {
    exact := hleft.left
    mono_f := hleft.right
    epi_g := s3_proper_pushforward_epi p hp hS hF
  }

theorem s3_injective_quotient_of_injective {C : Type*} [Category* C] [Abelian C]
    {S : ShortComplex C} (hS : S.ShortExact) [Injective S.X₁] [Injective S.X₂] :
    Injective S.X₃ := by
  let h := hS.splittingOfInjective
  constructor
  intro A B g f hf
  obtain ⟨k, hk⟩ := Injective.factors (g ≫ h.s) f
  refine ⟨k ≫ S.g, ?_⟩
  rw [← Category.assoc, hk, Category.assoc, h.s_g, Category.comp_id]

end HodgeLean.Foundations.Program
