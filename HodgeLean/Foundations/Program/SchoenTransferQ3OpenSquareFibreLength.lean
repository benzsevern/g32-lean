import HodgeLean.Foundations.Program.SchoenTransferQ3OpenFibreLength

/-! Unreduced point-fibre length through the actual ambient open square. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- Restricting both ambient spaces to actual opens retains point-fibre
length for the specified commuting map. -/
theorem s4_q3_point_fibre_length_open_square
    {X W X' W' : Scheme} (i : X' ⟶ X) (j : W' ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion j] (q : X ⟶ W) (q' : X' ⟶ W')
    (hsquare : i ≫ q = q' ≫ j) (p : X') :
    SingularCycles.pointFibreLength q' p = SingularCycles.pointFibreLength q (i p) := by
  let e := W.presheaf.stalkCongr (Inseparable.of_eq
    (congrArg (fun k : X' ⟶ W => k p) hsquare))
  let a := e.hom ≫ j.stalkMap (q' p)
  let b := i.stalkMap p
  have ha : Function.Surjective a.hom :=
    (ConcreteCategory.bijective_of_isIso (j.stalkMap (q' p))).2.comp
      (ConcreteCategory.bijective_of_isIso e.hom).2
  have hb := ConcreteCategory.bijective_of_isIso b
  have hcomm : b.hom.comp (q.stalkMap (i p)).hom = (q'.stalkMap p).hom.comp a.hom := by
    have hs : q.stalkMap (i p) ≫ i.stalkMap p =
        e.hom ≫ j.stalkMap (q' p) ≫ q'.stalkMap p := by
      rw [← Scheme.Hom.stalkMap_comp, ← Scheme.Hom.stalkMap_comp]
      exact Scheme.Hom.stalkMap_congr_hom _ _ hsquare p
    exact congrArg CommRingCat.Hom.hom hs
  have hker : RingHom.ker b.hom ≤
      (IsLocalRing.maximalIdeal (W.presheaf.stalk (q (i p)))).map (q.stalkMap (i p)).hom := by
    intro x hx
    change b.hom x = 0 at hx
    have hx0 : x = 0 := hb.1 (hx.trans (map_zero b.hom).symm)
    rw [hx0]
    exact Ideal.zero_mem _
  exact (s4_q3_fibre_length_surjective_square (q.stalkMap (i p)).hom a.hom
    b.hom (q'.stalkMap p).hom ha hb.2 hcomm hker).symm

/-- Openness of the specified original map passes through the actual
commuting ambient open square. -/
theorem s4_q3_isOpenMap_of_ambient_open_square
    {X W X' W' : Scheme} (i : X' ⟶ X) (j : W' ⟶ W)
    [IsOpenImmersion i] [IsOpenImmersion j] (q : X ⟶ W) (q' : X' ⟶ W')
    (hsquare : i ≫ q = q' ≫ j) (hq : IsOpenMap q) : IsOpenMap q' := by
  have hcomp : IsOpenMap (fun x => j (q' x)) := by
    have hmap : (fun x => j (q' x)) = (fun x => q (i x)) := by
      funext x
      exact (congrArg (fun m : X' ⟶ W => m x) hsquare).symm
    rw [hmap]
    exact hq.comp i.isOpenEmbedding.isOpenMap
  intro O hO
  have hop := (hcomp O hO).preimage j.continuous
  have heq : j ⁻¹' ((fun x => j (q' x)) '' O) = q' '' O := by
    ext w
    constructor
    · rintro ⟨x, hx, he⟩
      exact ⟨x, hx, j.isOpenEmbedding.injective he⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨x, hx, rfl⟩
  exact heq ▸ hop

end HodgeLean.Foundations.Program
