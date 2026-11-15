import HodgeLean.Foundations.Program.CurveJacobianA2Elliptic

noncomputable section

set_option maxHeartbeats 400000

open Manifold

namespace HodgeLean.Foundations.Program

/-- A horizontal coordinate loop translated by one half in the vertical direction. -/
def CurveJacobianA2_loopAhalf : b3_SmoothLoop b3_EllipticModel b3_Elliptic :=
  ⟨fun t ↦ b3_ellipticPoint t (1 / 2),
    fun t ↦ (b3_ellipticPoint_add_one t (1 / 2)).1,
    by
      convert (b3A_torusLine b2_stdF (b3A_e 0) ((1 / 2 : ℝ) • b3A_e 1)).1 using 1
      funext u
      rw [b3A_ellipticPoint_eq]
      rfl⟩

/-- A vertical coordinate loop translated by one half in the horizontal direction. -/
def CurveJacobianA2_loopBhalf : b3_SmoothLoop b3_EllipticModel b3_Elliptic :=
  ⟨fun t ↦ b3_ellipticPoint (1 / 2) t,
    fun t ↦ (b3_ellipticPoint_add_one (1 / 2) t).2,
    by
      convert (b3A_torusLine b2_stdF (b3A_e 1) ((1 / 2 : ℝ) • b3A_e 0)).1 using 1
      funext u
      rw [b3A_ellipticPoint_eq]
      congr 1
      rw [add_comm]
      rw [RCLike.real_smul_eq_coe_smul (K := ℂ)]
      norm_num
      ⟩

/-- The half-translated horizontal loop has the same period as `a`. -/
theorem CurveJacobianA2_period_loopAhalf :
    b3_latticePeriod _ _ CurveJacobianA2_loopAhalf = b3_latticePeriod _ _ b3A_loopA := by
  apply Subtype.ext
  funext θ
  change b3_pathPeriod _ _ (fun t ↦ b3_ellipticPoint t (1 / 2)) θ =
    b3_pathPeriod _ _ b3_ellipticA θ
  rw [show (fun t : ℝ ↦ b3_ellipticPoint t (1 / 2)) =
      fun t : ℝ ↦ QuotientAddGroup.mk ((t : ℂ) • b3A_e 0 + ((1 / 2 : ℝ) : ℂ) • b3A_e 1) by
        funext t; rw [b3A_ellipticPoint_eq],
    b3A_ellipticA_eq, b3A_line_pathPeriod, b3A_line_pathPeriod]

/-- The half-translated vertical loop has the same period as `b`. -/
theorem CurveJacobianA2_period_loopBhalf :
    b3_latticePeriod _ _ CurveJacobianA2_loopBhalf = b3_latticePeriod _ _ b3A_loopB := by
  apply Subtype.ext
  funext θ
  change b3_pathPeriod _ _ (fun t ↦ b3_ellipticPoint (1 / 2) t) θ =
    b3_pathPeriod _ _ b3_ellipticB θ
  rw [show (fun t : ℝ ↦ b3_ellipticPoint (1 / 2) t) =
      fun t : ℝ ↦ QuotientAddGroup.mk ((t : ℂ) • b3A_e 1 + ((1 / 2 : ℝ) : ℂ) • b3A_e 0) by
        funext t; rw [b3A_ellipticPoint_eq]; congr 1; abel,
    b3A_ellipticB_eq, b3A_line_pathPeriod, b3A_line_pathPeriod]

/-- The horizontal coordinate loop and its half-translate are disjoint. -/
theorem CurveJacobianA2_loopA_disjoint (s t : ℝ) :
    b3A_loopA.1 s ≠ CurveJacobianA2_loopAhalf.1 t := by
  intro h
  change b3_ellipticPoint s 0 = b3_ellipticPoint t (1 / 2) at h
  rw [b3A_ellipticPoint_eq, b3A_ellipticPoint_eq] at h
  obtain ⟨x, hx⟩ := (QuotientAddGroup.eq).1 h
  have hz := congrArg b3A_φ hx
  simp only [b3A_φ_latticeMap, map_add, map_neg, map_smul,
    b3A_φ_e0, b3A_φ_e1, smul_eq_mul] at hz
  have hi := congrArg Complex.im hz
  norm_num at hi
  have hi' : (2 * (x 1 : ℝ)) = 1 := by linarith
  have : (2 * x 1 : ℤ) = 1 := by exact_mod_cast hi'
  omega

/-- The vertical coordinate loop and its half-translate are disjoint. -/
theorem CurveJacobianA2_loopB_disjoint (s t : ℝ) :
    b3A_loopB.1 s ≠ CurveJacobianA2_loopBhalf.1 t := by
  intro h
  change b3_ellipticPoint 0 s = b3_ellipticPoint (1 / 2) t at h
  rw [b3A_ellipticPoint_eq, b3A_ellipticPoint_eq] at h
  obtain ⟨x, hx⟩ := (QuotientAddGroup.eq).1 h
  have hz := congrArg b3A_φ hx
  simp only [b3A_φ_latticeMap, map_add, map_neg, map_smul,
    b3A_φ_e0, b3A_φ_e1, smul_eq_mul] at hz
  have hr := congrArg Complex.re hz
  norm_num at hr
  have hr' : (2 * (x 0 : ℝ)) = 1 := by linarith
  have : (2 * x 0 : ℤ) = 1 := by exact_mod_cast hr'
  omega

/-- Each coordinate loop is transverse to its disjoint half-translate. -/
theorem CurveJacobianA2_coordinate_transverse :
    b3_Transverse b3_EllipticModel b3A_loopA CurveJacobianA2_loopAhalf ∧
      b3_Transverse b3_EllipticModel b3A_loopB CurveJacobianA2_loopBhalf := by
  constructor <;> intro s t h
  · exact (CurveJacobianA2_loopA_disjoint s t h).elim
  · exact (CurveJacobianA2_loopB_disjoint s t h).elim

/-- The coordinate loops have zero intersection with their disjoint half-translates. -/
theorem CurveJacobianA2_coordinate_half_intersection :
    b3_intersection b3_EllipticModel b3A_loopA CurveJacobianA2_loopAhalf = 0 ∧
      b3_intersection b3_EllipticModel b3A_loopB CurveJacobianA2_loopBhalf = 0 := by
  constructor
  · have hc : b3_crossings b3_EllipticModel b3A_loopA CurveJacobianA2_loopAhalf = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp ↦ CurveJacobianA2_loopA_disjoint _ _ hp.2.2
    simp [b3_intersection, hc]
  · have hc : b3_crossings b3_EllipticModel b3A_loopB CurveJacobianA2_loopBhalf = ∅ :=
      Set.eq_empty_of_forall_notMem fun p hp ↦ CurveJacobianA2_loopB_disjoint _ _ hp.2.2
    simp [b3_intersection, hc]

/-- Values of an elliptic intersection form on the coordinate periods. -/
theorem CurveJacobianA2_intersectionForm_values
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm b3_EllipticModel Q) :
    Q (b3_latticePeriod _ _ b3A_loopA) (b3_latticePeriod _ _ b3A_loopA) = 0 ∧
    Q (b3_latticePeriod _ _ b3A_loopB) (b3_latticePeriod _ _ b3A_loopB) = 0 ∧
    Q (b3_latticePeriod _ _ b3A_loopA) (b3_latticePeriod _ _ b3A_loopB) = 1 ∧
    Q (b3_latticePeriod _ _ b3A_loopB) (b3_latticePeriod _ _ b3A_loopA) = -1 := by
  let la := b3_latticePeriod b3_EllipticModel b3_Elliptic b3A_loopA
  let lb := b3_latticePeriod b3_EllipticModel b3_Elliptic b3A_loopB
  have hQaa : Q la la = 0 := by
    calc
      Q la la = Q la (b3_latticePeriod _ _ CurveJacobianA2_loopAhalf) :=
        congrArg (Q la) CurveJacobianA2_period_loopAhalf.symm
      _ = 0 := (hQ _ _ CurveJacobianA2_coordinate_transverse.1).trans
        CurveJacobianA2_coordinate_half_intersection.1
  have hQbb : Q lb lb = 0 := by
    calc
      Q lb lb = Q lb (b3_latticePeriod _ _ CurveJacobianA2_loopBhalf) :=
        congrArg (Q lb) CurveJacobianA2_period_loopBhalf.symm
      _ = 0 := (hQ _ _ CurveJacobianA2_coordinate_transverse.2).trans
        CurveJacobianA2_coordinate_half_intersection.2
  have hab : b3_Transverse b3_EllipticModel b3A_loopA b3A_loopB :=
    b3A_elliptic_transverse _ _ rfl rfl
  have hba : b3_Transverse b3_EllipticModel b3A_loopB b3A_loopA := by
    intro s t h
    change b3_orient b3_EllipticModel
      (b3_velocity _ _ b3_ellipticB s) (b3_velocity _ _ b3_ellipticA t) ≠ 0
    rw [b3A_velocity_ellipticB, b3A_velocity_ellipticA,
      b3A_orient_swap (E := b3_EllipticModel)]
    have hp := (b3A_orient_ab t s).ne'
    rw [b3A_velocity_ellipticA, b3A_velocity_ellipticB] at hp
    exact neg_ne_zero.mpr hp
  have hQab : Q la lb = 1 :=
    (hQ _ _ hab).trans (b3A_elliptic_intersection _ _ rfl rfl)
  have hQba : Q lb la = -1 := by
    rw [hQ _ _ hba, b3A_intersection_antisymm (E := b3_EllipticModel),
      b3A_elliptic_intersection b3A_loopA b3A_loopB rfl rfl]
  exact ⟨hQaa, hQbb, hQab, hQba⟩

/-- Two bilinear forms agreeing on two spanning generators agree everywhere. -/
theorem CurveJacobianA2_bilin_eq_of_span {M : Type} [AddCommGroup M] [Module ℤ M]
    (a b : M) (hspan : ∀ u : M, ∃ m n : ℤ, u = m • a + n • b)
    (Q Q' : LinearMap.BilinForm ℤ M)
    (haa : Q a a = Q' a a) (hbb : Q b b = Q' b b)
    (hab : Q a b = Q' a b) (hba : Q b a = Q' b a) : Q = Q' := by
  apply LinearMap.ext
  intro u
  apply LinearMap.ext
  intro v
  obtain ⟨m, n, hu⟩ := hspan u
  obtain ⟨r, s, hv⟩ := hspan v
  rw [hu, hv]
  simp only [map_add, map_zsmul, LinearMap.add_apply, LinearMap.smul_apply,
    haa, hbb, hab, hba]

/-- The prescribed alternating form is the elliptic intersection form. -/
theorem CurveJacobianA2_elliptic_intersectionForm_eq
    (Q : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ : b3_IsIntersectionForm b3_EllipticModel Q)
    (Q' : LinearMap.BilinForm ℤ (b3_periodLattice b3_EllipticModel b3_Elliptic))
    (hQ'alt : ∀ x, Q' x x = 0)
    (hQ'ab : Q' (b3_latticePeriod _ _ b3A_loopA) (b3_latticePeriod _ _ b3A_loopB) = 1) :
    Q = Q' := by
  let la := b3_latticePeriod b3_EllipticModel b3_Elliptic b3A_loopA
  let lb := b3_latticePeriod b3_EllipticModel b3_Elliptic b3A_loopB
  obtain ⟨hQaa, hQbb, hQab, hQba⟩ := CurveJacobianA2_intersectionForm_values Q hQ
  have hQ'aa : Q' la la = 0 := hQ'alt la
  have hQ'bb : Q' lb lb = 0 := hQ'alt lb
  have hQ'ab' : Q' la lb = 1 := hQ'ab
  have hQ'ba : Q' lb la = -1 := by
    have hz := hQ'alt (la + lb)
    have hz' : Q' la la + Q' lb la + (Q' la lb + Q' lb lb) = 0 := by
      simpa only [map_add, LinearMap.add_apply] using hz
    omega
  exact CurveJacobianA2_bilin_eq_of_span la lb CurveJacobianA2_latticePeriod_span Q Q'
    (hQaa.trans hQ'aa.symm) (hQbb.trans hQ'bb.symm) (hQab.trans hQ'ab'.symm)
    (hQba.trans hQ'ba.symm)

end HodgeLean.Foundations.Program
