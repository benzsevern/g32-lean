import HodgeLean.Foundations.Program.SchoenTransferQ3CartesianStalkSquare

/-! Scheme-theoretic kernel of an actual cartesian immersion on stalks. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
namespace HodgeLean.Foundations.Program

/-- The kernel of the actual base-changed immersion is the extension of the
original immersion kernel through the actual stalk map. -/
theorem s4_q3_closed_pullback_stalk_kernel
    {W Z C : Scheme} (t : W ⟶ Z) (i : C ⟶ Z) [IsClosedImmersion i]
    (d : (pullback t i : Scheme)) :
    let e := Z.presheaf.stalkCongr (Inseparable.of_eq
      (congrArg (fun k : pullback t i ⟶ Z => k d) (pullback.condition (f := t) (g := i))))
    RingHom.ker ((pullback.fst t i).stalkMap d).hom =
      (RingHom.ker (e.hom ≫ i.stalkMap (pullback.snd t i d)).hom).map
        (t.stalkMap (pullback.fst t i d)).hom := by
  let w := pullback.fst t i d
  let c := pullback.snd t i d
  let e := Z.presheaf.stalkCongr (Inseparable.of_eq
    (congrArg (fun k : pullback t i ⟶ Z => k d) (pullback.condition (f := t) (g := i))))
  let f := t.stalkMap w
  let p := e.hom ≫ i.stalkMap c
  let q := (pullback.fst t i).stalkMap d
  let g := (pullback.snd t i).stalkMap d
  have hcomm : f ≫ q = p ≫ g := s4_q3_closed_pullback_stalk_square t i d
  let J := (RingHom.ker p.hom).map f.hom
  have hle : J ≤ RingHom.ker q.hom := by
    rw [Ideal.map_le_iff_le_comap, RingHom.comap_ker]
    change RingHom.ker p.hom ≤ RingHom.ker (f ≫ q).hom
    rw [hcomm]
    intro a ha
    change g.hom (p.hom a) = 0
    rw [ha, map_zero]
  let D := (W.presheaf.stalk w) ⧸ J
  have hJ : J ≠ ⊤ := ne_top_of_le_ne_top (RingHom.ker_ne_top q.hom) hle
  letI : Nontrivial D := Ideal.Quotient.nontrivial_iff.mpr hJ
  letI : IsLocalRing D := IsLocalRing.of_surjective' (Ideal.Quotient.mk J)
    Ideal.Quotient.mk_surjective
  let v : W.presheaf.stalk w ⟶ CommRingCat.of D := CommRingCat.ofHom (Ideal.Quotient.mk J)
  have : IsLocalHom v.hom := IsLocalHom.of_surjective v.hom Ideal.Quotient.mk_surjective
  have hp : Function.Surjective p.hom :=
    (i.stalkMap_surjective c).comp (ConcreteCategory.bijective_of_isIso e.hom).2
  have hpv : RingHom.ker p.hom ≤ RingHom.ker (f ≫ v).hom := by
    intro a ha
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_map_of_mem f.hom ha)
  let l : C.presheaf.stalk c ⟶ CommRingCat.of D :=
    CommRingCat.ofHom (p.hom.liftOfSurjective hp ⟨(f ≫ v).hom, hpv⟩)
  have hpl : p ≫ l = f ≫ v := by
    exact CommRingCat.hom_ext (RingHom.liftOfSurjective_comp p.hom hp _)
  let kw := Spec.map v ≫ W.fromSpecStalk w
  let kc := Spec.map l ≫ C.fromSpecStalk c
  have hcone : kw ≫ t = kc ≫ i := by
    dsimp only [kw, kc]
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Spec.map_comp_assoc]
    have he : Spec.map e.hom ≫ Z.fromSpecStalk (t w) = Z.fromSpecStalk (i c) :=
      by
        dsimp only [e, TopCat.Presheaf.stalkCongr]
        exact Scheme.SpecMap_stalkSpecializes_fromSpecStalk _
    change Spec.map (f ≫ v) ≫ Z.fromSpecStalk (t w) = _
    rw [← hpl]
    dsimp only [p]
    rw [Category.assoc, Spec.map_comp, Category.assoc, he]
  let k := pullback.lift kw kc hcone
  have hkd : k (IsLocalRing.closedPoint (CommRingCat.of D)) = d := by
    apply (pullback.fst t i).isClosedEmbedding.injective
    change (k ≫ pullback.fst t i) _ = w
    rw [pullback.lift_fst]
    change W.fromSpecStalk w (Spec.map v (IsLocalRing.closedPoint (CommRingCat.of D))) = w
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  obtain ⟨r, hr⟩ := s4_q3_factor_fromSpecStalk_at_closedPoint (CommRingCat.of D) k d hkd
  have hqr : q ≫ r = v := by
    apply Spec.map_injective
    apply (cancel_mono (W.fromSpecStalk w)).mp
    rw [Spec.map_comp, Category.assoc, Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, hr]
    exact pullback.lift_fst ..
  apply le_antisymm _ hle
  intro a ha
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change v.hom a = 0
  rw [← hqr]
  change r.hom (q.hom a) = 0
  rw [ha, map_zero]

end HodgeLean.Foundations.Program
