import HodgeLean.Foundations.RationalHomologyManifold.LocallyStationaryMaps

/-! Natural morphisms obtained from actual locally stationary presheaf-map sequences.
HC no distance; AV milestone no distance.
-/
noncomputable section
set_option maxHeartbeats 200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
namespace HodgeLean.Foundations.RationalHomologyManifold

/-- Locally stationary actual morphisms into a sheaf glue to a natural additive morphism.
Source: Bredon, Sheaf Theory, second edition, I.1; uniqueness of gluing and naturality on germs.
HC no distance; AV milestone no distance.
-/
def locallyStationaryPresheafMap {X : TopCat.{0}} (P : TopCat.Presheaf AddCommGrpCat.{0} X)
    (F : TopCat.Sheaf AddCommGrpCat.{0} X) (f : ℕ → (P ⟶ F.obj))
    (hlocal : ∀ (U : Opens X) (a : P.obj (op U)), ∀ x : U,
      ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
        F.obj.map (homOfLE hV).op ((f (m + r)).app (op U) a) =
          F.obj.map (homOfLE hV).op ((f m).app (op U) a)) : P ⟶ F.obj where
  app U := locallyStationarySectionMap (P.obj U) F U.unop (fun m => (f m).app U) (hlocal U.unop)
  naturality {U V} i := by
    ext a
    change P.obj U at a
    apply TopCat.Presheaf.section_ext F
    intro x hxV
    have hxU : x ∈ U.unop := leOfHom i.unop hxV
    obtain ⟨m, hm⟩ := locallyStationarySectionMap_germ_eventually (P.obj V) F V.unop
      (fun m => (f m).app V) (hlocal V.unop) (P.map i a) ⟨x, hxV⟩
    obtain ⟨n, hn⟩ := locallyStationarySectionMap_germ_eventually (P.obj U) F U.unop
      (fun m => (f m).app U) (hlocal U.unop) a ⟨x, hxU⟩
    have hn' := hn m
    rw [Nat.add_comm n m] at hn'
    have hf := ConcreteCategory.congr_hom ((f (m + n)).naturality i) a
    simp only [ConcreteCategory.comp_apply] at hf
    calc
      _ = F.presheaf.germ V.unop x hxV ((f (m + n)).app V (P.map i a)) := hm n
      _ = F.presheaf.germ V.unop x hxV (F.obj.map i ((f (m + n)).app U a)) :=
        congrArg (F.presheaf.germ V.unop x hxV) hf
      _ = F.presheaf.germ U.unop x hxU ((f (m + n)).app U a) :=
        F.presheaf.germ_res_apply (i := i.unop) x hxV _
      _ = F.presheaf.germ U.unop x hxU
          (locallyStationarySectionMap (P.obj U) F U.unop (fun m => (f m).app U) (hlocal U.unop) a) := hn'.symm
      _ = _ := (F.presheaf.germ_res_apply (i := i.unop) x hxV _).symm

#print axioms locallyStationaryPresheafMap
/-- The actual glued presheaf morphism retains the eventual germs of its original finite morphisms.
Source: Bredon, Sheaf Theory, second edition, I.1; the normalized stationary presheaf gluing.
HC no distance; AV milestone no distance.
-/
theorem locallyStationaryPresheafMap_germ_eventually {X : TopCat.{0}}
    (P : TopCat.Presheaf AddCommGrpCat.{0} X) (F : TopCat.Sheaf AddCommGrpCat.{0} X)
    (f : ℕ → (P ⟶ F.obj))
    (hlocal : ∀ (U : Opens X) (a : P.obj (op U)), ∀ x : U,
      ∃ (V : Opens X) (hV : V ≤ U), x.val ∈ V ∧ ∃ m : ℕ, ∀ r : ℕ,
        F.obj.map (homOfLE hV).op ((f (m + r)).app (op U) a) =
          F.obj.map (homOfLE hV).op ((f m).app (op U) a)) (U : Opens X) (a : P.obj (op U)) :
    ∀ x : U, ∃ m : ℕ, ∀ r : ℕ,
      F.presheaf.germ U x.val x.property ((locallyStationaryPresheafMap P F f hlocal).app (op U) a) =
        F.presheaf.germ U x.val x.property ((f (m + r)).app (op U) a) :=
  locallyStationarySectionMap_germ_eventually (P.obj (op U)) F U (fun m => (f m).app (op U))
    (hlocal U) a

#print axioms locallyStationaryPresheafMap_germ_eventually
end HodgeLean.Foundations.RationalHomologyManifold
