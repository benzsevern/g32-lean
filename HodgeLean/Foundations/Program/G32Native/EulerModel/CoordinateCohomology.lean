import HodgeLean.Foundations.Program.G32Native.EulerModel.SmoothIntegralProduct

/-! # Actual cohomology classes of coordinate linear subspaces -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4096
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
open CategoryTheory AlgebraicGeometry AlgebraicGeometry.ComplexPoint TopologicalSpace
open HodgeLean.Adapters HodgeLean.RealDefs HodgeLean.Foundations.Program
namespace HodgeLean.Foundations.Program.G32Native.EulerModel

/-- The canonical component class of the actual retained coordinate linear subspace. -/
def coordinate_cycle_class
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) : HQ Q (2 * T.card) := by
  let E := coordinate_intersection_class Q k eQ T hT
  let hI := Classical.choose E
  letI := hI
  exact cycleComponentSheafClass Q
    ((s2c_subschemeι Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left
      (genericPoint (s2c_subscheme Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left))
    (Classical.choose_spec E).2.1

/-- The coordinate class uses the same actual generic point with any integral instance. -/
theorem coordinate_cycle_class_eq
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (T : Finset (Fin (k + 1))) (hT : T.card ≤ k)
    [IsIntegral (s2c_subscheme Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left]
    (hc : Order.coheight
      ((s2c_subschemeι Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left
        (genericPoint (s2c_subscheme Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left)) = T.card) :
    coordinate_cycle_class Q k eQ T hT = cycleComponentSheafClass Q _ hc := by
  rfl

#print axioms coordinate_cycle_class
#print axioms coordinate_cycle_class_eq
/-- The same actual coordinate class transported along an explicit codimension equality. -/
def coordinate_class_at_degree
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) (n : ℕ) (hn : T.card = n) : HQ Q (2 * n) := by
  subst n
  exact coordinate_cycle_class Q k eQ T hT

/-- Explicit degree transport retains the actual component class and its codimension proof. -/
theorem coordinate_class_at_degree_eq
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (T : Finset (Fin (k + 1))) (hT : T.card ≤ k) (n : ℕ) (hn : T.card = n)
    [IsIntegral (s2c_subscheme Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left]
    (hc : Order.coheight
      ((s2c_subschemeι Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left
        (genericPoint (s2c_subscheme Q ((s2e_s2b_intersectionIdeal k T).comap eQ.hom.left)).left)) = n) :
    coordinate_class_at_degree Q k eQ T hT n hn = cycleComponentSheafClass Q _ hc := by
  subst n
  exact coordinate_cycle_class_eq Q k eQ T hT hc

#print axioms coordinate_class_at_degree
#print axioms coordinate_class_at_degree_eq
/-- Coordinate intersections of additive codimension represent products of their actual classes. -/
theorem coordinate_class_at_degree_cup
    (Q : Over (Spec ↧ℂ)) [IsIntegral Q.left] [Smooth Q.hom] [IsProjective Q.hom]
    (k : ℕ) (eQ : Q ≅ Over.mk (ProjectiveSpace.toBase (Fin (k + 1)) (Spec ↧ℂ)))
    (T U : Finset (Fin (k + 1)))
    (hT : T.card ≤ k) (hU : U.card ≤ k) (hTU : (T ∪ U).card ≤ k)
    (p q : ℕ) (hp : T.card = p) (hq : U.card = q) (hpq : (T ∪ U).card = p + q) :
    (cupProductOf Q).cup (by change 2 * p + 2 * q = 2 * (p + q); omega)
      (coordinate_class_at_degree Q k eQ T hT p hp)
      (coordinate_class_at_degree Q k eQ U hU q hq) =
      coordinate_class_at_degree Q k eQ (T ∪ U) hTU (p + q) hpq := by
  let I := (s2e_s2b_intersectionIdeal k T).comap eQ.hom.left
  let J := (s2e_s2b_intersectionIdeal k U).comap eQ.hom.left
  let K := (s2e_s2b_intersectionIdeal k (T ∪ U)).comap eQ.hom.left
  obtain ⟨hI, hsmI, hcI, -⟩ := coordinate_intersection_class Q k eQ T hT
  obtain ⟨hJ, hsmJ, hcJ, -⟩ := coordinate_intersection_class Q k eQ U hU
  obtain ⟨hK, hsmK, hcK, -⟩ := coordinate_intersection_class Q k eQ (T ∪ U) hTU
  letI : IsIntegral I.subscheme := hI
  letI : IsIntegral J.subscheme := hJ
  letI : IsIntegral K.subscheme := hK
  letI : Smooth (I.subschemeι ≫ Q.hom) := hsmI
  letI : Smooth (J.subschemeι ≫ Q.hom) := hsmJ
  letI : Smooth (K.subschemeι ≫ Q.hom) := hsmK
  have hsum : I ⊔ J = K := by
    dsimp only [I, J, K]
    rw [coordinate_intersection_ideal_union, Scheme.IdealSheafData.comap_sup]
  letI : IsIntegral (I ⊔ J).subscheme := by rw [hsum]; infer_instance
  letI : Smooth ((I ⊔ J).subschemeι ≫ Q.hom) := by rw [hsum]; infer_instance
  change Order.coheight (I.subschemeι (genericPoint I.subscheme)) = T.card at hcI
  change Order.coheight (J.subschemeι (genericPoint J.subscheme)) = U.card at hcJ
  change Order.coheight (K.subschemeι (genericPoint K.subscheme)) = (T ∪ U).card at hcK
  have hpoint := subscheme_generic_point_congr Q (I ⊔ J) K hsum
  have hIp : Order.coheight (I.subschemeι (genericPoint I.subscheme)) = p := by simpa only [hp] using hcI
  have hJq : Order.coheight (J.subschemeι (genericPoint J.subscheme)) = q := by simpa only [hq] using hcJ
  have hKpq : Order.coheight (K.subschemeι (genericPoint K.subscheme)) = p + q := by simpa only [hpq, Nat.cast_add] using hcK
  rw [coordinate_class_at_degree_eq Q k eQ T hT p hp hIp,
    coordinate_class_at_degree_eq Q k eQ U hU q hq hJq,
    coordinate_class_at_degree_eq Q k eQ (T ∪ U) hTU (p + q) hpq hKpq]
  change (cupProductOf Q).cup _
    (cycleComponentSheafClass Q (I.subschemeι (genericPoint I.subscheme)) hIp)
    (cycleComponentSheafClass Q (J.subschemeι (genericPoint J.subscheme)) hJq) =
    cycleComponentSheafClass Q (K.subschemeι (genericPoint K.subscheme)) hKpq
  have h := smooth_integral_subscheme_cup Q I J p q hIp hJq (by rw [hpoint]; exact hKpq)
  simpa only [hpoint] using h

#print axioms coordinate_class_at_degree_cup
end HodgeLean.Foundations.Program.G32Native.EulerModel
