import HodgeLean.Foundations.Program.SchoenFiniteSchemeProducts

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Coordinate morphisms determine the actual morphism between ordered finite scheme products. -/
def s2_schemeProductMap : (n : ℕ) → (Y Z : Fin n → Scheme.{0}) →
    (∀ i, Y i ⟶ Z i) → (s2_schemeProduct n Y ⟶ s2_schemeProduct n Z)
  | 0, _, _, _ => 𝟙 _
  | n + 1, Y, Z, f => pullback.map _ _ _ _ (f 0)
      (s2_schemeProductMap n (fun i => Y i.succ) (fun i => Z i.succ) (fun i => f i.succ))
      (𝟙 _) (terminal.hom_ext _ _) (terminal.hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual product map has its prescribed equation on each coordinate. -/
theorem s2_schemeProductMap_π (n : ℕ) (Y Z : Fin n → Scheme.{0})
    (f : ∀ i, Y i ⟶ Z i) (i : Fin n) :
    s2_schemeProductMap n Y Z f ≫ s2_schemeProductπ n Z i =
      s2_schemeProductπ n Y i ≫ f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · simp only [s2_schemeProductMap, s2_schemeProductπ, Fin.cases_zero,
        pullback.map, pullback.lift_fst]
    · change s2_schemeProductMap (n + 1) Y Z f ≫
        (pullback.snd _ _ ≫ s2_schemeProductπ n (fun k => Z k.succ) j) =
          (pullback.snd _ _ ≫ s2_schemeProductπ n (fun k => Y k.succ) j) ≫ f j.succ
      simp only [s2_schemeProductMap, pullback.map, pullback.lift_snd_assoc]
      rw [Category.assoc, ih]
      exact (Category.assoc _ _ _).symm

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Coordinatewise open immersions induce an open immersion of actual finite scheme products. -/
theorem s2_schemeProductMap_isOpenImmersion (n : ℕ) (Y Z : Fin n → Scheme.{0})
    (f : ∀ i, Y i ⟶ Z i) [∀ i, IsOpenImmersion (f i)] :
    IsOpenImmersion (s2_schemeProductMap n Y Z f) := by
  induction n with
  | zero => exact inferInstanceAs (IsOpenImmersion (𝟙 (terminal Scheme)))
  | succ n ih =>
    haveI := ih (fun i => Y i.succ) (fun i => Z i.succ) (fun i => f i.succ)
    dsimp only [s2_schemeProductMap]
    infer_instance

end HodgeLean.Foundations.Program
