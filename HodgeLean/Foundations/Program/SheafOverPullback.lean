module

public import HodgeLean.Foundations.Program.SingularCochainSheafPullback

@[expose] public section
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory
namespace HodgeLean.Foundations.Program

/-- Pullback along a map over the base acts on direct images over that base.
Source: Bredon, Sheaf Theory, second edition, I.3, direct image. -/
def sheafOverPullback {A B : TopCat} (q : A ⟶ B) (f : A ⟶ A)
    (hf : f ≫ q = q) {F F' : TopCat.Sheaf AddCommGrpCat A}
    (l : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj F') :
    (TopCat.Sheaf.pushforward AddCommGrpCat q).obj F ⟶
      (TopCat.Sheaf.pushforward AddCommGrpCat q).obj F' :=
  (TopCat.Sheaf.pushforward AddCommGrpCat q).map l ≫
    eqToHom (by
      change (TopCat.Sheaf.pushforward AddCommGrpCat (f ≫ q)).obj F' = _
      rw [hf])

/-- Equality of continuous maps acts on direct-image sections by the corresponding open restriction.
Source: Bredon, Sheaf Theory, second edition, I.3, direct image. -/
theorem pushforward_eq_app {A B : TopCat} (r q : A ⟶ B) (h : r = q)
    (F : TopCat.Sheaf AddCommGrpCat A) (U : (TopologicalSpace.Opens B)ᵒᵖ) :
    (eqToHom (congrArg (fun z => (TopCat.Sheaf.pushforward AddCommGrpCat z).obj F) h)).hom.app U =
      F.obj.map (eqToHom (congrArg (fun z =>
        (TopologicalSpace.Opens.map z).obj U.unop) h.symm)).op := by
  subst q
  simp only [eqToHom_refl, op_id]
  change 𝟙 _ = F.obj.map (𝟙 _)
  exact (F.obj.map_id _).symm

/-- A compatible square of sheaf maps remains compatible over the fixed base.
Source: Bredon, Sheaf Theory, second edition, I.3, functoriality of direct image. -/
theorem sheafOverPullback_naturality {A B : TopCat} (q : A ⟶ B) (f : A ⟶ A)
    (hf : f ≫ q = q) {F F' K K' : TopCat.Sheaf AddCommGrpCat A}
    (l : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj F')
    (m : K ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj K')
    (b : F ⟶ K) (b' : F' ⟶ K')
    (h : b ≫ m = l ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f).map b') :
    (TopCat.Sheaf.pushforward AddCommGrpCat q).map b ≫ sheafOverPullback q f hf m =
      sheafOverPullback q f hf l ≫ (TopCat.Sheaf.pushforward AddCommGrpCat q).map b' := by
  unfold sheafOverPullback
  rw [← Category.assoc, ← Functor.map_comp, h, Functor.map_comp, Category.assoc]
  exact congrArg ((TopCat.Sheaf.pushforward AddCommGrpCat q).map l ≫ ·)
    (eqToHom_naturality
      (fun r : A ⟶ B => (TopCat.Sheaf.pushforward AddCommGrpCat r).map b') hf)

/-- Pullback over a fixed base acts degreewise on cochain complexes of sheaves.
Source: Bredon, Sheaf Theory, second edition, II.4, complexes and direct image. -/
def cochainOverPullback {A B : TopCat} (q : A ⟶ B) (f : A ⟶ A)
    (hf : f ≫ q = q) {K K' : CochainComplex (TopCat.Sheaf AddCommGrpCat A) ℕ}
    (l : K ⟶ ((TopCat.Sheaf.pushforward AddCommGrpCat f).mapHomologicalComplex
      (.up ℕ)).obj K') :
    ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).obj K ⟶
      ((TopCat.Sheaf.pushforward AddCommGrpCat q).mapHomologicalComplex (.up ℕ)).obj K' where
  f n := sheafOverPullback q f hf (l.f n)
  comm' i j hij := (sheafOverPullback_naturality q f hf (l.f i) (l.f j)
    (K.d i j) (K'.d i j) (l.comm i j).symm).symm

/-- On global sections the map over the base is the original sheaf pullback.
Source: Bredon, Sheaf Theory, second edition, I.3, global sections of direct images. -/
theorem sheafOverPullback_top {A B : TopCat} (q : A ⟶ B) (f : A ⟶ A)
    (hf : f ≫ q = q) {F F' : TopCat.Sheaf AddCommGrpCat A}
    (l : F ⟶ (TopCat.Sheaf.pushforward AddCommGrpCat f).obj F') :
    (sheafOverPullback q f hf l).hom.app (Opposite.op ⊤) = l.hom.app (Opposite.op ⊤) := by
  change l.hom.app (Opposite.op ⊤) ≫
    (eqToHom (congrArg (fun z => (TopCat.Sheaf.pushforward AddCommGrpCat z).obj F') hf) :
      (TopCat.Sheaf.pushforward AddCommGrpCat (f ≫ q)).obj F' ⟶
        (TopCat.Sheaf.pushforward AddCommGrpCat q).obj F').hom.app (Opposite.op ⊤) = _
  rw [pushforward_eq_app (f ≫ q) q hf]
  have he : (eqToHom (congrArg (fun z =>
      (TopologicalSpace.Opens.map z).obj ⊤) hf.symm)).op = 𝟙 (Opposite.op (⊤ : TopologicalSpace.Opens A)) :=
    Subsingleton.elim _ _
  rw [he]
  exact (congrArg (l.hom.app (Opposite.op ⊤) ≫ ·) (F'.obj.map_id _)).trans
    (Category.comp_id _)

end HodgeLean.Foundations.Program
