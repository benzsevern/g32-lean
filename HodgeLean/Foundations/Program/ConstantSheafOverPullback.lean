import HodgeLean.Foundations.Program.SheafOverPullback
import HodgeLean.Foundations.Program.FiniteQuotientSheafTrace

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory TopologicalSpace Opposite
namespace HodgeLean.Foundations.Program

/-- Pullback over the quotient base has the actual composition formula on constant sections.
Source: Bredon, Sheaf Theory, second edition, I.3, direct image and constant sheaves. -/
theorem constantSheafOverPullback_sections {A B : TopCat.{0}}
    (q : A ⟶ B) (f : A ⟶ A) (hf : f ≫ q = q)
    (L : 𝓒(A; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj 𝓒(A; ℚ))
    (hL : ∀ (V : Opens A) (s : 𝓒(A; ℚ).obj.obj (op V)) (x : f ⁻¹' V),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map f).obj V)
        (L.hom.app (op V) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) V s ⟨f x, x.property⟩)
    (U : Opens B) (s : 𝓒(A; ℚ).obj.obj (op ((Opens.map q).obj U)))
    (x : q ⁻¹' U) :
    constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
      ((sheafOverPullback q f hf L).hom.app (op U) s) x =
    constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U) s
      ⟨f x, by
        have h := congrArg (fun k : A ⟶ B => k x) hf
        change q (f x) = q x at h
        change q (f x) ∈ U
        rw [h]
        exact x.property⟩ := by
  let V := (Opens.map q).obj U
  let W := (Opens.map (f ≫ q)).obj U
  have hWV : W = V := congrArg (fun z => (Opens.map z).obj U) hf
  have hle : V ≤ W := by rw [hWV]
  change constantSheafSectionEquiv (AddCommGrpCat.of ℚ) V
    ((eqToHom (congrArg (fun z => (TopCat.Sheaf.pushforward AddCommGrpCat z).obj 𝓒(A; ℚ)) hf) :
      (TopCat.Sheaf.pushforward AddCommGrpCat (f ≫ q)).obj 𝓒(A; ℚ) ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ)).hom.app
      (op U) (L.hom.app (op V) s)) x = _
  rw [pushforward_eq_app (f ≫ q) q hf]
  have he : (eqToHom (congrArg (fun z => (Opens.map z).obj U) hf.symm)).op =
      (homOfLE hle).op := Subsingleton.elim _ _
  rw [he]
  exact (constantSheafSectionEquiv_restrict (X := A) (AddCommGrpCat.of ℚ) W V hle
    (L.hom.app (op V) s) x).trans (hL V s ⟨x, hle x.property⟩)

/-- The opposite constant-sheaf trace is the sum of the actual action pullbacks.
Source: Bredon, Introduction to Compact Transformation Groups (1972),
Chapter III, section 7, finite orbit transfer. -/
theorem constantSheafOverPullback_trace_norm {A B : TopCat.{0}}
    (G : Type) [Fintype G] (q : A ⟶ B) (a : G → (A ⟶ A))
    (ha : ∀ g, a g ≫ q = q)
    (L : 𝓒(B; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ))
    (T : (TopCat.Sheaf.pushforward AddCommGrpCat q).obj 𝓒(A; ℚ) ⟶ 𝓒(B; ℚ))
    (hL : ∀ (U : Opens B) (s : 𝓒(B; ℚ).obj.obj (op U)) (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        (L.hom.app (op U) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U s ⟨q x, x.property⟩)
    (hT : ∀ (U : Opens B) (s : 𝓒(A; ℚ).obj.obj (op ((Opens.map q).obj U)))
      (x : q ⁻¹' U),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) U (T.hom.app (op U) s)
        ⟨q x, x.property⟩ =
      ∑ g : G, constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U)
        s ⟨a g x, by
          have h := congrArg (fun k : A ⟶ B => k x) (ha g)
          change q (a g x) = q x at h
          change q (a g x) ∈ U
          rw [h]
          exact x.property⟩)
    (La : ∀ g, 𝓒(A; ℚ) ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat (a g)).obj 𝓒(A; ℚ))
    (hLa : ∀ g (V : Opens A) (s : 𝓒(A; ℚ).obj.obj (op V)) (x : a g ⁻¹' V),
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map (a g)).obj V)
        ((La g).hom.app (op V) s) x =
      constantSheafSectionEquiv (AddCommGrpCat.of ℚ) V s ⟨a g x, x.property⟩) :
    T ≫ L = ∑ g : G, sheafOverPullback q (a g) (ha g) (La g) := by
  classical
  apply CategoryTheory.Sheaf.hom_ext
  ext U s
  apply (constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U.unop)).injective
  apply LocallyConstant.ext
  intro x
  have hinv (g : G) (x : A) : q (a g x) = q x :=
    congrArg (fun k : A ⟶ B => k x) (ha g)
  rw [finite_quotient_constantSheaf_trace_norm G (fun g => a g) q hinv L T hL hT]
  have he : ((∑ g : G, sheafOverPullback q (a g) (ha g) (La g)).hom.app U) s =
      ∑ g : G, (sheafOverPullback q (a g) (ha g) (La g)).hom.app U s := by
    induction Finset.univ (α := G) using Finset.induction_on with
    | empty => rfl
    | @insert g S hg ih =>
      simp only [Finset.sum_insert hg]
      change (sheafOverPullback q (a g) (ha g) (La g)).hom.app U s + _ = _
      exact congrArg ((sheafOverPullback q (a g) (ha g) (La g)).hom.app U s + ·) ih
  rw [he, map_sum]
  change _ = LocallyConstant.evalAddMonoidHom x (∑ g : G,
    constantSheafSectionEquiv (AddCommGrpCat.of ℚ) ((Opens.map q).obj U.unop)
      ((sheafOverPullback q (a g) (ha g) (La g)).hom.app U s))
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro g _
  exact (constantSheafOverPullback_sections q (a g) (ha g) (La g) (hLa g) U.unop s x).symm

end HodgeLean.Foundations.Program
