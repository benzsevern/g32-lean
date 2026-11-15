module

public import HodgeLean.Foundations.Program.SchoenExceptionalProperExact

@[expose] public noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open scoped AlgebraicGeometry
namespace HodgeLean.Foundations.Program

attribute [local instance] TopCat.Sheaf.extAddCommGroup

set_option backward.isDefEq.respectTransparency false in
theorem s3_sections_surjective_of_split_pushforward {X Y : TopCat.{0}} (p : X ⟶ Y)
    {S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X)}
    (hS : (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p)).ShortExact)
    [Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj S.X₁)] :
    Function.Surjective (S.g.hom.app (op ⊤)) := by
  let R := S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p)
  let : Injective R.X₁ := inferInstanceAs
    (Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj S.X₁))
  let h : R.Splitting := hS.splittingOfInjective
  change Function.Surjective (R.g.hom.app (op ⊤))
  intro c
  refine ⟨h.s.hom.app (op ⊤) c, ?_⟩
  have e := congrArg (fun f : R.X₃ ⟶ R.X₃ => f.hom.app (op ⊤)) h.s_g
  exact congrArg (fun f => f c) e

set_option backward.isDefEq.respectTransparency false in
theorem s3_proper_cohomology_succ_eq_zero {X Y : TopCat.{0}}
    [T2Space X] [LocallyCompactSpace X] (p : X ⟶ Y) (hp : IsProperMap p)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hF : ∀ (y : Y) (q : ℕ), Subsingleton (CategoryTheory.Sheaf.H
      ((TopCat.Sheaf.pullback AddCommGrpCat.{0} (s3_fibreInclusion p y)).obj F) (q + 1)))
    (hP : Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj F))
    (n : ℕ) (x : Abelian.Ext 𝓒(X; ULift ℤ) F (n + 1)) : x = 0 := by
  induction n generalizing F with
  | zero =>
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      let : Injective S.X₂ := by dsimp [S]; infer_instance
      let : Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj S.X₁) := hP
      have hPS := s3_proper_pushforward_shortExact p hp hS (fun y => hF y 0)
      have hx : x.comp (Abelian.Ext.mk₀ S.f) (add_zero 1) = 0 := by
        apply Abelian.Ext.eq_zero_of_injective
      obtain ⟨a, ha⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx rfl
      obtain ⟨b, hb⟩ := s3_sections_surjective_of_split_pushforward p hPS
        (s3_globalSectionsEquiv S.X₃ a)
      let b' : Abelian.Ext 𝓒(X; ULift ℤ) S.X₂ 0 :=
        (s3_globalSectionsEquiv S.X₂).symm b
      have hb' : b'.comp (Abelian.Ext.mk₀ S.g) (add_zero 0) = a := by
        apply (s3_globalSectionsEquiv S.X₃).injective
        rw [← s3_globalSectionsEquiv_naturality]
        simpa only [b', Equiv.apply_symm_apply] using hb
      rw [← ha, ← hb', Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
        Abelian.Ext.comp_zero]
  | succ n ih =>
      let S : ShortComplex (TopCat.Sheaf AddCommGrpCat.{0} X) :=
        ShortComplex.mk (Injective.ι F) (cokernel.π (Injective.ι F))
          (cokernel.condition (Injective.ι F))
      have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel (Injective.ι F) }
      let : Injective S.X₂ := by dsimp [S]; infer_instance
      let : Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj S.X₁) := hP
      let : Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj S.X₂) :=
        s3_pushforward_injective p S.X₂
      have hPS := s3_proper_pushforward_shortExact p hp hS (fun y => hF y 0)
      let : Injective (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p)).X₁ := hP
      let : Injective (S.map (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p)).X₂ :=
        s3_pushforward_injective p S.X₂
      have hP₃ : Injective ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj S.X₃) :=
        s3_injective_quotient_of_injective hPS
      have h₃ := s3_fibre_cokernel_acyclic p hp hS hF
      have hx : x.comp (Abelian.Ext.mk₀ S.f) (add_zero (n + 2)) = 0 := by
        apply Abelian.Ext.eq_zero_of_injective
      obtain ⟨a, ha⟩ := Abelian.Ext.covariant_sequence_exact₁ _ hS x hx rfl
      have ha0 : a = 0 := ih S.X₃ h₃ hP₃ a
      rw [← ha, ha0]
      exact Abelian.Ext.zero_comp _ _ _ _ _


set_option backward.isDefEq.respectTransparency false in
theorem s3_H_zero_of_pushforward_isZero {X Y : TopCat.{0}} (p : X ⟶ Y)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (hP : IsZero ((TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj F)) :
    Subsingleton (CategoryTheory.Sheaf.H F 0) := by
  let P := (TopCat.Sheaf.pushforward AddCommGrpCat.{0} p).obj F
  let : Subsingleton (CategoryTheory.Sheaf.H P 0) :=
    CategoryTheory.Sheaf.subsingleton_H_of_isZero hP 0
  let e := s3_globalSectionsEquiv P
  let : Subsingleton (P.obj.obj (op ⊤)) := e.symm.injective.subsingleton
  let : Subsingleton (F.obj.obj (op ⊤)) := inferInstanceAs (Subsingleton (P.obj.obj (op ⊤)))
  exact (s3_globalSectionsEquiv F).injective.subsingleton

end HodgeLean.Foundations.Program
