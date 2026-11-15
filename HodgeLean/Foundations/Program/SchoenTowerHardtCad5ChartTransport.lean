import HodgeLean.Foundations.Program.SchoenTowerHardtCad5GraphImages
import HodgeLean.Foundations.Program.SchoenTowerHardtCad4Sub

/-! Transport of an actual box partition through supplied Boolean chart graphs. -/
noncomputable section
set_option maxHeartbeats 400000
set_option synthInstance.maxHeartbeats 400000
namespace HodgeLean.Foundations.Program

theorem s2v_hardt_cad5_chart_partition_transport {n d : ℕ}
    (C : s2v_t11b_Formula n)
    (e : C.realize ≃ₜ {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
    (G : s2v_t11b_Formula (n + d))
    (hG : ∀ (x : C.realize) (z : EuclideanSpace ℝ (Fin d)),
      WithLp.toLp 2 (Fin.append (fun v => x.val v) (fun v => z v)) ∈ G.realize ↔ z = (e x).val)
    (J : s2v_t11b_Formula (d + n))
    (hJ : ∀ (z : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1})
      (x : EuclideanSpace ℝ (Fin n)),
      WithLp.toLp 2 (Fin.append (fun v => z.val v) (fun v => x v)) ∈ J.realize ↔ x = (e.symm z).val)
    (hdn : d ≤ n)
    (P : s2v_hardt_cad5_Partition {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1}) :
    ∃ Q : s2v_hardt_cad5_Partition C.realize, ∃ p : Fin Q.count ≃ Fin P.count,
      (∀ i, Q.dim i = P.dim (p i)) ∧
      (∀ i (x : C.realize), x.val ∈ (Q.cell i).realize ↔ (e x).val ∈ (P.cell (p i)).realize) ∧
      Q.dimension = P.dimension ∧
      (∀ i, IsOpen (P.cell (p i)).realize → IsOpen {x : C.realize | x.val ∈ (Q.cell i).realize}) := by
  classical
  have hsub (i : Fin P.count) : (P.cell i).realize ⊆
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} := by
    intro z hz
    have hu : z ∈ ⋃ l, (P.cell l).realize := Set.mem_iUnion.mpr ⟨i, hz⟩
    simpa only [P.cover] using hu
  have formula (i : Fin P.count) : ∃ c : s2v_t11b_Formula n,
      ∀ x, x ∈ c.realize ↔ ∃ a : C.realize, x = a.val ∧ (e a).val ∈ (P.cell i).realize := by
    obtain ⟨c, hc⟩ := s2v_hardt_cad5_relation_image_formula (P.cell i) J
    refine ⟨c, ?_⟩
    intro x
    rw [hc]
    constructor
    · rintro ⟨z, hz⟩
      let b : {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} := ⟨z.val, hsub i z.property⟩
      have he := (hJ b x).mp hz
      exact ⟨e.symm b, he, by simpa only [e.apply_symm_apply] using z.property⟩
    · rintro ⟨a, rfl, ha⟩
      refine ⟨⟨(e a).val, ha⟩, (hJ (e a) a.val).mpr ?_⟩
      simp only [e.symm_apply_apply]
  choose c hc using formula
  let toC (i : Fin P.count) (x : (c i).realize) : C.realize :=
    ⟨x.val, by obtain ⟨a, he, _⟩ := (hc i x.val).mp x.property; rw [he]; exact a.property⟩
  let intoBox (i : Fin P.count) (z : (P.cell i).realize) :
      {z : EuclideanSpace ℝ (Fin d) | ∀ v, -1 < z v ∧ z v < 1} := ⟨z.val, hsub i z.property⟩
  have hmem (i : Fin P.count) (x : (c i).realize) : (e (toC i x)).val ∈ (P.cell i).realize := by
    obtain ⟨a, he, ha⟩ := (hc i x.val).mp x.property
    have hea : toC i x = a := Subtype.ext he
    rw [hea]
    exact ha
  have hinvmem (i : Fin P.count) (z : (P.cell i).realize) :
      (e.symm (intoBox i z)).val ∈ (c i).realize := by
    exact (hc i _).mpr ⟨e.symm (intoBox i z), rfl, by simpa only [e.apply_symm_apply] using z.property⟩
  let pull (i : Fin P.count) : (c i).realize ≃ₜ (P.cell i).realize :=
    { toFun := fun x => ⟨(e (toC i x)).val, hmem i x⟩
      invFun := fun z => ⟨(e.symm (intoBox i z)).val, hinvmem i z⟩
      left_inv := by
        intro x
        apply Subtype.ext
        change (e.symm (intoBox i ⟨(e (toC i x)).val, hmem i x⟩)).val = x.val
        have he : intoBox i ⟨(e (toC i x)).val, hmem i x⟩ = e (toC i x) := Subtype.ext rfl
        rw [he, e.symm_apply_apply]
      right_inv := by
        intro z
        apply Subtype.ext
        change (e (toC i ⟨(e.symm (intoBox i z)).val, hinvmem i z⟩)).val = z.val
        have he : toC i ⟨(e.symm (intoBox i z)).val, hinvmem i z⟩ = e.symm (intoBox i z) := Subtype.ext rfl
        rw [he, e.apply_symm_apply]
      continuous_toFun := by
        apply Continuous.subtype_mk
        exact (e.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val
      continuous_invFun := by
        apply Continuous.subtype_mk
        exact (e.symm.continuous.comp (continuous_subtype_val.subtype_mk _)).subtype_val }
  have composites := fun i => s2v_hardt_cad4_sub_compose C e G hG J hJ (c i) (P.cell i)
    (toC i) (fun _ => rfl) (intoBox i) (fun _ => rfl) (pull i) (fun _ => rfl) (fun _ => rfl)
    (P.chart i) (P.forward i) (P.forward_eq i) (P.inverse i) (P.inverse_eq i)
  choose E F I hEF hEI hE hEinv hEval using composites
  have hn (i : Fin P.count) : (c i).realize.Nonempty := by
    obtain ⟨z, hz⟩ := P.nonempty i
    exact ⟨(pull i).symm ⟨z, hz⟩, ((pull i).symm ⟨z, hz⟩).property⟩
  have hd : Pairwise (fun i j => Disjoint (c i).realize (c j).realize) := by
    intro i j hij
    apply Set.disjoint_left.mpr
    intro x hxi hxj
    obtain ⟨a, ha, hai⟩ := (hc i x).mp hxi
    obtain ⟨b, hb, hbj⟩ := (hc j x).mp hxj
    have he : a = b := Subtype.ext (ha.symm.trans hb)
    subst b
    exact Set.disjoint_left.mp (P.disjoint hij) hai hbj
  have hu : (⋃ i, (c i).realize) = C.realize := by
    ext x
    constructor
    · intro hx
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp hx
      obtain ⟨a, rfl, _⟩ := (hc i x).mp hi
      exact a.property
    · intro hx
      let a : C.realize := ⟨x, hx⟩
      have he : (e a).val ∈ ⋃ i, (P.cell i).realize := by
        simpa only [P.cover] using (e a).property
      obtain ⟨i, hi⟩ := Set.mem_iUnion.mp he
      exact Set.mem_iUnion.mpr ⟨i, (hc i x).mpr ⟨a, rfl, hi⟩⟩
  let Q : s2v_hardt_cad5_Partition C.realize :=
    { count := P.count, cell := c, dim := P.dim, chart := E, forward := F, inverse := I
      nonempty := hn, disjoint := hd, cover := hu
      bound := fun i => (P.bound i).trans hdn
      forward_eq := hEF, inverse_eq := hEI }
  have hMembership (i : Fin Q.count) (x : C.realize) :
      x.val ∈ (Q.cell i).realize ↔ (e x).val ∈ (P.cell i).realize := by
    change x.val ∈ (c i).realize ↔ (e x).val ∈ (P.cell i).realize
    rw [hc i]
    constructor
    · rintro ⟨a, ha, hai⟩
      have he : x = a := Subtype.ext ha
      simpa only [he] using hai
    · intro hx
      exact ⟨x, rfl, hx⟩
  refine ⟨Q, Equiv.refl _, fun _ => rfl, hMembership, rfl, ?_⟩
  intro i hi
  have hset : {x : C.realize | x.val ∈ (Q.cell i).realize} =
      (fun x : C.realize => (e x).val) ⁻¹' (P.cell i).realize := by
    ext x
    exact hMembership i x
  rw [hset]
  exact hi.preimage e.continuous.subtype_val

end HodgeLean.Foundations.Program
