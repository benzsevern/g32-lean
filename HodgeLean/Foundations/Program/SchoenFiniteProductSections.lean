import HodgeLean.Foundations.Program.SchoenFiniteSchemeProducts
import Mathlib.AlgebraicGeometry.Morphisms.Affine

noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Every global section on the actual terminal scheme is an integer constant. -/
theorem s2_terminalSections_intCast_surjective :
    Function.Surjective (Int.castRingHom Γ(terminal Scheme.{0}, ⊤)) := by
  let e := terminalIsTerminal.uniqueUpToIso specZIsTerminal
  let c := (Scheme.ΓSpecIso (CommRingCat.of ℤ)).symm ≪≫ Scheme.Γ.mapIso e.op
  have hc : c.hom.hom = Int.castRingHom Γ(terminal Scheme.{0}, ⊤) := Subsingleton.elim _ _
  rw [← hc]
  exact c.commRingCatIsoToRingEquiv.surjective

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
/-- Global sections on a finite product of affine schemes are generated as a ring by the actual coordinate pullbacks. -/
theorem s2_schemeProduct_sections_mem (n : ℕ) (Y : Fin n → Scheme.{0})
    [∀ i, IsAffine (Y i)] (S : Subring Γ(s2_schemeProduct n Y, ⊤))
    (hS : ∀ i, ∀ a : Γ(Y i, ⊤), (s2_schemeProductπ n Y i).appTop a ∈ S)
    (a : Γ(s2_schemeProduct n Y, ⊤)) : a ∈ S := by
  haveI : IsAffine (terminal Scheme) :=
    IsAffine.of_isIso (terminalIsTerminal.uniqueUpToIso specZIsTerminal).hom
  induction n with
  | zero =>
    obtain ⟨z, rfl⟩ := s2_terminalSections_intCast_surjective a
    exact intCast_mem S z
  | succ n ih =>
    let T := s2_schemeProduct n (fun i => Y i.succ)
    haveI : IsAffine T := s2_schemeProduct_isAffine n _
    let p : s2_schemeProduct (n + 1) Y ⟶ Y 0 := pullback.fst _ _
    let q : s2_schemeProduct (n + 1) Y ⟶ T := pullback.snd _ _
    have hq : ∀ b : Γ(T, ⊤), q.appTop b ∈ S := by
      intro b
      apply ih (fun i => Y i.succ) (S.comap q.appTop.hom) _ b
      intro i c
      simpa only [Subring.mem_comap, q, s2_schemeProductπ, Fin.cases_succ, Scheme.Hom.comp_appTop,
        CommRingCat.hom_comp, RingHom.comp_apply] using hS i.succ c
    let u : Γ(Y 0, ⊤) →+* S := p.appTop.hom.codRestrict S (hS 0)
    let v : Γ(T, ⊤) →+* S := q.appTop.hom.codRestrict S hq
    have H := isPushout_appTop_of_isPullback
      (IsPullback.of_hasPullback (terminal.from (Y 0)) (terminal.from T))
    have huv : (terminal.from (Y 0)).appTop ≫ CommRingCat.ofHom u =
        (terminal.from T).appTop ≫ CommRingCat.ofHom v := by
      apply CommRingCat.hom_ext
      ext c
      exact congrArg (fun f : Γ(terminal Scheme, ⊤) ⟶ Γ(s2_schemeProduct (n + 1) Y, ⊤) => f.hom c) H.w
    let d := H.desc (CommRingCat.ofHom u) (CommRingCat.ofHom v) huv
    have hd : d ≫ CommRingCat.ofHom S.subtype = 𝟙 _ := by
      apply H.hom_ext
      · rw [← Category.assoc, H.inl_desc]
        rfl
      · rw [← Category.assoc, H.inr_desc]
        rfl
    have ha : (d.hom a).val = a := congrArg (fun f : Γ(s2_schemeProduct (n + 1) Y, ⊤) ⟶ Γ(s2_schemeProduct (n + 1) Y, ⊤) => f.hom a) hd
    exact ha ▸ (d.hom a).property

end HodgeLean.Foundations.Program
