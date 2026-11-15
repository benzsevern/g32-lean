import Mathlib.AlgebraicGeometry.Pullbacks
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The actual finite scheme product over the terminal scheme, with ordered factors. -/
def s2_schemeProduct : (n : ℕ) → (Fin n → Scheme.{0}) → Scheme.{0}
  | 0, _ => terminal Scheme
  | n + 1, Y => pullback (terminal.from (Y 0))
      (terminal.from (s2_schemeProduct n (fun i => Y i.succ)))

/-- The coordinate projections of the actual finite scheme product. -/
def s2_schemeProductπ : (n : ℕ) → (Y : Fin n → Scheme.{0}) →
    (i : Fin n) → (s2_schemeProduct n Y ⟶ Y i)
  | 0, _, i => Fin.elim0 i
  | n + 1, Y, i => Fin.cases
      (pullback.fst (terminal.from (Y 0))
        (terminal.from (s2_schemeProduct n (fun j => Y j.succ))))
      (fun j => pullback.snd (terminal.from (Y 0))
        (terminal.from (s2_schemeProduct n (fun k => Y k.succ))) ≫
          s2_schemeProductπ n (fun k => Y k.succ) j) i

/-- A family of scheme morphisms determines its actual finite-product lift. -/
def s2_schemeProductLift {T : Scheme.{0}} : (n : ℕ) → (Y : Fin n → Scheme.{0}) →
    (∀ i, T ⟶ Y i) → (T ⟶ s2_schemeProduct n Y)
  | 0, _, _ => terminal.from T
  | n + 1, Y, f => pullback.lift (f 0)
      (s2_schemeProductLift n (fun i => Y i.succ) (fun i => f i.succ))
      (terminal.hom_ext _ _)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- The actual finite-product lift recovers each specified coordinate morphism. -/
theorem s2_schemeProductLift_π {T : Scheme.{0}} (n : ℕ) (Y : Fin n → Scheme.{0})
    (f : ∀ i, T ⟶ Y i) (i : Fin n) :
    s2_schemeProductLift n Y f ≫ s2_schemeProductπ n Y i = f i := by
  induction n with
  | zero => exact Fin.elim0 i
  | succ n ih =>
    refine Fin.cases ?_ (fun j => ?_) i
    · exact pullback.lift_fst _ _ _
    · change s2_schemeProductLift (n + 1) Y f ≫
        (pullback.snd _ _ ≫ s2_schemeProductπ n (fun k => Y k.succ) j) = f j.succ
      rw [← Category.assoc, s2_schemeProductLift, pullback.lift_snd]
      exact ih _ _ j

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Morphisms to the actual finite scheme product are determined by all their coordinates. -/
theorem s2_schemeProduct_hom_ext {T : Scheme.{0}} (n : ℕ) (Y : Fin n → Scheme.{0})
    (f g : T ⟶ s2_schemeProduct n Y)
    (h : ∀ i, f ≫ s2_schemeProductπ n Y i = g ≫ s2_schemeProductπ n Y i) : f = g := by
  induction n with
  | zero => exact terminal.hom_ext f g
  | succ n ih =>
    apply pullback.hom_ext
    · exact h 0
    · apply ih
      intro i
      exact (Category.assoc _ _ _).trans ((h i.succ).trans (Category.assoc _ _ _).symm)

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Finite products of actual affine schemes remain affine over the terminal scheme. -/
theorem s2_schemeProduct_isAffine (n : ℕ) (Y : Fin n → Scheme.{0})
    [∀ i, IsAffine (Y i)] : IsAffine (s2_schemeProduct n Y) := by
  haveI : IsAffine (terminal Scheme) :=
    IsAffine.of_isIso (terminalIsTerminal.uniqueUpToIso specZIsTerminal).hom
  induction n with
  | zero => exact inferInstanceAs (IsAffine (terminal Scheme))
  | succ n ih =>
    haveI := ih (fun i => Y i.succ)
    change IsAffine (pullback (terminal.from (Y 0))
      (terminal.from (s2_schemeProduct n (fun i => Y i.succ))))
    infer_instance

end HodgeLean.Foundations.Program
