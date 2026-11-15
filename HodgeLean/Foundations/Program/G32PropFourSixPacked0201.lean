import HodgeLean.Foundations.Program.G32PropFourSixPacked0200
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000

def g32p_integralPointScale (a : HurwitzPrymRex_Zw) (V : HurwitzPrymRex_Mat) :
    HurwitzPrymRex_Mat := fun i j => HurwitzPrymRex_Zw.mul a (V i j)

def g32p_integralPointAdd (V W : HurwitzPrymRex_Mat) : HurwitzPrymRex_Mat :=
  fun i j => HurwitzPrymRex_Zw.add (V i j) (W i j)

def g32p_integralPointPolynomial (M V : HurwitzPrymRex_Mat) :
    List HurwitzPrymRex_Zw → HurwitzPrymRex_Mat
  | [] => fun _ _ => ⟨0, 0⟩
  | a :: cs => g32p_integralPointAdd (g32p_integralPointScale a V)
      (HurwitzPrymRex_mmul M (g32p_integralPointPolynomial M V cs))

def g32p_matrixPointPolynomial (A V : Matrix (Fin 4) (Fin 4) ℂ) :
    List HurwitzPrymRex_Zw → Matrix (Fin 4) (Fin 4) ℂ
  | [] => 0
  | a :: cs => HurwitzPrymRex_ev g32h_omega a • V + A * g32p_matrixPointPolynomial A V cs

theorem g32p_integralPointScale_eval (a : HurwitzPrymRex_Zw) (V : HurwitzPrymRex_Mat) :
    HurwitzPrymRex_evM g32h_omega (g32p_integralPointScale a V) =
      HurwitzPrymRex_ev g32h_omega a • HurwitzPrymRex_evM g32h_omega V := by
  ext i j
  exact HurwitzPrymRex_ev_mul g32h_omega_sq_add _ _

theorem g32p_integralPointAdd_eval (V W : HurwitzPrymRex_Mat) :
    HurwitzPrymRex_evM g32h_omega (g32p_integralPointAdd V W) =
      HurwitzPrymRex_evM g32h_omega V + HurwitzPrymRex_evM g32h_omega W := by
  ext i j
  exact HurwitzPrymRex_ev_add _ _

theorem g32p_integralPointPolynomial_transport (M V : HurwitzPrymRex_Mat)
    (cs : List HurwitzPrymRex_Zw) :
    HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega (g32p_integralPointPolynomial M V cs) =
      g32p_matrixPointPolynomial (HurwitzPrymRex_g32conj (HurwitzPrymRex_evM g32h_omega M))
        (HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega V) cs := by
  induction cs with
  | nil =>
    have hz : HurwitzPrymRex_evM g32h_omega (g32p_integralPointPolynomial M V []) =
        (0 : Matrix (Fin 4) (Fin 4) ℂ) := by
      ext i j
      norm_num [g32p_integralPointPolynomial, HurwitzPrymRex_evM, HurwitzPrymRex_ev]
    rw [hz, g32p_matrixPointPolynomial, Matrix.mul_zero]
  | cons a cs ih =>
    rw [g32p_integralPointPolynomial, g32p_integralPointAdd_eval, Matrix.mul_add,
      g32p_integralPointScale_eval, Matrix.mul_smul,
      ← g32p_rootPoint_transport, ih]
    rfl

theorem g32p_matrixPointPolynomial_commute (A X V : Matrix (Fin 4) (Fin 4) ℂ)
    (h : Commute A X) (cs : List HurwitzPrymRex_Zw) :
    g32p_matrixPointPolynomial A (X * V) cs = X * g32p_matrixPointPolynomial A V cs := by
  induction cs with
  | nil => simp only [g32p_matrixPointPolynomial, Matrix.mul_zero]
  | cons a cs ih =>
    rw [g32p_matrixPointPolynomial, g32p_matrixPointPolynomial, Matrix.mul_add,
      Matrix.mul_smul, ih, ← Matrix.mul_assoc, h.eq, Matrix.mul_assoc]


theorem g32p_centralizer_point_polynomial (c : Fin 102)
    (x : Subgroup.centralizer {g32p_literalRepresentative c}) (i j₀ : Fin 240)
    (cs : List HurwitzPrymRex_Zw) (a : HurwitzPrymRex_Zw)
    (hi : b4b_toMatrix (x : g32p_G) * g32p_basePoint = g32p_rootPoint i)
    (hbase : g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix c)
      (g32p_rootMatrix 58) cs = g32p_integralPointScale a (g32p_rootMatrix j₀)) :
    ∃ j : Fin 240, g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix c)
      (g32p_rootMatrix i) cs = g32p_integralPointScale a (g32p_rootMatrix j) := by
  obtain ⟨j, hj⟩ := g32p_rootPoint_invariant (x : g32p_G) (g32p_rootPoint j₀) ⟨j₀, rfl⟩
  have hcomm : Commute (b4b_toMatrix (g32p_literalRepresentative c))
      (b4b_toMatrix (x : g32p_G)) := by
    apply (commute_iff_eq _ _).mpr
    simpa only [map_mul] using congrArg b4b_toMatrix
      (Subgroup.mem_centralizer_singleton_iff.mp x.property).symm
  have hb : g32p_matrixPointPolynomial (b4b_toMatrix (g32p_literalRepresentative c))
      g32p_basePoint cs = HurwitzPrymRex_ev g32h_omega a • g32p_rootPoint j₀ := by
    rw [g32p_basePoint_root]
    change g32p_matrixPointPolynomial _
      (HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega (g32p_rootMatrix 58)) cs = _
    rw [g32p_literalRepresentative_matrix, ← g32p_integralPointPolynomial_transport,
      hbase, g32p_integralPointScale_eval, Matrix.mul_smul]
    rfl
  refine ⟨j, ?_⟩
  apply HurwitzPrymRex_evM_injective g32h_omega_sq_add
  have h : HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega
      (g32p_integralPointPolynomial (g32p_literalRepresentativeMatrix c) (g32p_rootMatrix i) cs) =
      HurwitzPrymRex_g32P * HurwitzPrymRex_evM g32h_omega
        (g32p_integralPointScale a (g32p_rootMatrix j)) := by
    rw [g32p_integralPointPolynomial_transport, ← g32p_literalRepresentative_matrix,
      g32p_integralPointScale_eval, Matrix.mul_smul]
    change g32p_matrixPointPolynomial _ (g32p_rootPoint i) cs =
      HurwitzPrymRex_ev g32h_omega a • g32p_rootPoint j
    rw [← hi, g32p_matrixPointPolynomial_commute _ _ _ hcomm, hb,
      Matrix.mul_smul, ← hj]
  have hh := congrArg (fun A : Matrix (Fin 4) (Fin 4) ℂ => HurwitzPrymRex_g32Pinv * A) h
  simpa only [← Matrix.mul_assoc, HurwitzPrymRex_g32_Pinv_P, Matrix.one_mul] using hh

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound001_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 52, 54, 55, 57, 58, 59, 61, 64, 65, 66, 67, 68, 69, 71, 73, 74, 77, 78, 79, 81, 83, 84, 85, 86, 87, 88, 89, 91, 93, 95, 96, 98, 99, 100, 102, 105, 106, 107, 108, 109, 110, 112, 114, 115, 118, 119, 120, 122, 124, 125, 126, 127, 128, 130, 131, 134, 136, 137, 138, 140, 141, 144, 145, 146, 148, 149, 151, 154, 155, 156, 157, 158, 159, 161, 163, 164, 167, 168, 169, 171, 173, 174, 175, 176, 178, 179, 182, 184, 185, 186, 188, 191, 192, 193, 195, 196, 198, 200, 203, 204, 206, 209, 210, 212, 213, 215, 216, 219, 220, 222, 225, 226, 227, 228, 231, 233, 234, 236, 237}

def g32p_centralizerBound001_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (8, 3), (8, 4), (8, 5), (10, 3), (10, 4), (10, 5), (16, 1), (16, 2), (16, 8), (18, 1), (18, 2), (18, 8), (49, 3), (49, 4), (49, 5), (60, 3), (60, 4), (60, 5), (68, 0), (68, 6), (68, 7)}

theorem g32p_centralizerBound001_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) := by
  decide +kernel

theorem g32p_centralizerBound001_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 1) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound001_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound001_point_block00 t
  · exact g32p_centralizerBound001_point_block01 t
  · exact g32p_centralizerBound001_point_block02 t
  · exact g32p_centralizerBound001_point_block03 t
  · exact g32p_centralizerBound001_point_block04 t
  · exact g32p_centralizerBound001_point_block05 t
  · exact g32p_centralizerBound001_point_block06 t
  · exact g32p_centralizerBound001_point_block07 t
  · exact g32p_centralizerBound001_point_block08 t
  · exact g32p_centralizerBound001_point_block09 t
  · exact g32p_centralizerBound001_point_block10 t
  · exact g32p_centralizerBound001_point_block11 t
  · exact g32p_centralizerBound001_point_block12 t
  · exact g32p_centralizerBound001_point_block13 t
  · exact g32p_centralizerBound001_point_block14 t

theorem g32p_centralizerBound001_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 1) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 1)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound001_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound001_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 1) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 1)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound001_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound001_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 1) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 1)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound001_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound001_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 1) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 1)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound001_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound001_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 1) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 1)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound001_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound001_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 1) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 1) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound001_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 1) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 1)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound001_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound001_stabilizer_block00 t r
  · exact g32p_centralizerBound001_stabilizer_block01 t r
  · exact g32p_centralizerBound001_stabilizer_block02 t r
  · exact g32p_centralizerBound001_stabilizer_block03 t r
  · exact g32p_centralizerBound001_stabilizer_block04 t r

theorem g32p_centralizerBound001_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 1}) ≤ g32p_literalCentralizer 1 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 1 g32p_centralizerBound001_points
    g32p_centralizerBound001_stabilizers ?_ g32p_centralizerBound001_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound001_point_mem i (g32p_centralizer_point_moments 1 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound002_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 52, 54, 55, 57, 58, 59, 61, 64, 65, 66, 67, 68, 69, 71, 73, 74, 77, 78, 79, 81, 83, 84, 85, 86, 87, 88, 89, 91, 93, 95, 96, 98, 99, 100, 102, 105, 106, 107, 108, 109, 110, 112, 114, 115, 118, 119, 120, 122, 124, 125, 126, 127, 128, 130, 131, 134, 136, 137, 138, 140, 141, 144, 145, 146, 148, 149, 151, 154, 155, 156, 157, 158, 159, 161, 163, 164, 167, 168, 169, 171, 173, 174, 175, 176, 178, 179, 182, 184, 185, 186, 188, 191, 192, 193, 195, 196, 198, 200, 203, 204, 206, 209, 210, 212, 213, 215, 216, 219, 220, 222, 225, 226, 227, 228, 231, 233, 234, 236, 237}

def g32p_centralizerBound002_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (8, 3), (8, 4), (8, 5), (10, 3), (10, 4), (10, 5), (16, 1), (16, 2), (16, 8), (18, 1), (18, 2), (18, 8), (49, 3), (49, 4), (49, 5), (60, 3), (60, 4), (60, 5), (68, 0), (68, 6), (68, 7)}

theorem g32p_centralizerBound002_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) := by
  decide +kernel

theorem g32p_centralizerBound002_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 2) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound002_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound002_point_block00 t
  · exact g32p_centralizerBound002_point_block01 t
  · exact g32p_centralizerBound002_point_block02 t
  · exact g32p_centralizerBound002_point_block03 t
  · exact g32p_centralizerBound002_point_block04 t
  · exact g32p_centralizerBound002_point_block05 t
  · exact g32p_centralizerBound002_point_block06 t
  · exact g32p_centralizerBound002_point_block07 t
  · exact g32p_centralizerBound002_point_block08 t
  · exact g32p_centralizerBound002_point_block09 t
  · exact g32p_centralizerBound002_point_block10 t
  · exact g32p_centralizerBound002_point_block11 t
  · exact g32p_centralizerBound002_point_block12 t
  · exact g32p_centralizerBound002_point_block13 t
  · exact g32p_centralizerBound002_point_block14 t

theorem g32p_centralizerBound002_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 2) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 2)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound002_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound002_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 2) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 2)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound002_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound002_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 2) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 2)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound002_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound002_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 2) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 2)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound002_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound002_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 2) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 2)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound002_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound002_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 2) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 2) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound002_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 2) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 2)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound002_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound002_stabilizer_block00 t r
  · exact g32p_centralizerBound002_stabilizer_block01 t r
  · exact g32p_centralizerBound002_stabilizer_block02 t r
  · exact g32p_centralizerBound002_stabilizer_block03 t r
  · exact g32p_centralizerBound002_stabilizer_block04 t r

theorem g32p_centralizerBound002_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 2}) ≤ g32p_literalCentralizer 2 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 2 g32p_centralizerBound002_points
    g32p_centralizerBound002_stabilizers ?_ g32p_centralizerBound002_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound002_point_mem i (g32p_centralizer_point_moments 2 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound003_points : Finset (Fin 240) :=
  {3, 6, 15, 26, 30, 33, 36, 48, 52, 55, 58, 61, 64, 65, 71, 81, 85, 89, 93, 96, 99, 102, 105, 106, 112, 122, 126, 130, 140, 144, 151, 154, 155, 161, 171, 175, 178, 188, 191, 200, 210, 212, 215, 222, 225, 228, 234, 236}

def g32p_centralizerBound003_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (22, 7), (24, 2), (30, 4), (36, 5), (53, 8), (63, 3), (68, 7)}

theorem g32p_centralizerBound003_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) := by
  decide +kernel

theorem g32p_centralizerBound003_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 3) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound003_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound003_point_block00 t
  · exact g32p_centralizerBound003_point_block01 t
  · exact g32p_centralizerBound003_point_block02 t
  · exact g32p_centralizerBound003_point_block03 t
  · exact g32p_centralizerBound003_point_block04 t
  · exact g32p_centralizerBound003_point_block05 t
  · exact g32p_centralizerBound003_point_block06 t
  · exact g32p_centralizerBound003_point_block07 t
  · exact g32p_centralizerBound003_point_block08 t
  · exact g32p_centralizerBound003_point_block09 t
  · exact g32p_centralizerBound003_point_block10 t
  · exact g32p_centralizerBound003_point_block11 t
  · exact g32p_centralizerBound003_point_block12 t
  · exact g32p_centralizerBound003_point_block13 t
  · exact g32p_centralizerBound003_point_block14 t

theorem g32p_centralizerBound003_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 3) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 3)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound003_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound003_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 3) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 3)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound003_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound003_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 3) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 3)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound003_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound003_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 3) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 3)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound003_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound003_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 3) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 3)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound003_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound003_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 3) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 3) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound003_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 3) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 3)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound003_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound003_stabilizer_block00 t r
  · exact g32p_centralizerBound003_stabilizer_block01 t r
  · exact g32p_centralizerBound003_stabilizer_block02 t r
  · exact g32p_centralizerBound003_stabilizer_block03 t r
  · exact g32p_centralizerBound003_stabilizer_block04 t r

theorem g32p_centralizerBound003_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 3}) ≤ g32p_literalCentralizer 3 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 3 g32p_centralizerBound003_points
    g32p_centralizerBound003_stabilizers ?_ g32p_centralizerBound003_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound003_point_mem i (g32p_centralizer_point_moments 3 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound004_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 28, 32, 33, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 50, 54, 55, 57, 58, 59, 61, 64, 66, 67, 69, 77, 79, 83, 84, 85, 86, 87, 88, 89, 91, 95, 96, 98, 99, 100, 102, 105, 107, 108, 110, 118, 120, 124, 125, 126, 127, 128, 130, 131, 134, 140, 141, 144, 145, 148, 151, 154, 156, 157, 159, 167, 169, 173, 174, 175, 176, 178, 179, 182, 188, 191, 192, 195, 213, 215, 216, 222, 225, 226}

def g32p_centralizerBound004_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (26, 1), (26, 2), (26, 8)}

theorem g32p_centralizerBound004_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) := by
  decide +kernel

theorem g32p_centralizerBound004_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 4) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound004_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound004_point_block00 t
  · exact g32p_centralizerBound004_point_block01 t
  · exact g32p_centralizerBound004_point_block02 t
  · exact g32p_centralizerBound004_point_block03 t
  · exact g32p_centralizerBound004_point_block04 t
  · exact g32p_centralizerBound004_point_block05 t
  · exact g32p_centralizerBound004_point_block06 t
  · exact g32p_centralizerBound004_point_block07 t
  · exact g32p_centralizerBound004_point_block08 t
  · exact g32p_centralizerBound004_point_block09 t
  · exact g32p_centralizerBound004_point_block10 t
  · exact g32p_centralizerBound004_point_block11 t
  · exact g32p_centralizerBound004_point_block12 t
  · exact g32p_centralizerBound004_point_block13 t
  · exact g32p_centralizerBound004_point_block14 t

theorem g32p_centralizerBound004_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 4) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 4)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound004_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound004_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 4) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 4)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound004_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound004_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 4) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 4)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound004_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound004_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 4) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 4)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound004_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound004_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 4) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 4)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound004_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound004_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 4) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 4) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound004_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 4) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 4)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound004_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound004_stabilizer_block00 t r
  · exact g32p_centralizerBound004_stabilizer_block01 t r
  · exact g32p_centralizerBound004_stabilizer_block02 t r
  · exact g32p_centralizerBound004_stabilizer_block03 t r
  · exact g32p_centralizerBound004_stabilizer_block04 t r

theorem g32p_centralizerBound004_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 4}) ≤ g32p_literalCentralizer 4 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 4 g32p_centralizerBound004_points
    g32p_centralizerBound004_stabilizers ?_ g32p_centralizerBound004_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound004_point_mem i (g32p_centralizer_point_moments 4 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound005_points : Finset (Fin 240) :=
  {3, 6, 9, 11, 15, 18, 20, 26, 30, 33, 35, 36, 37, 40, 42, 48, 52, 55, 57, 58, 59, 61, 64, 65, 67, 69, 71, 73, 74, 77, 81, 83, 85, 89, 93, 96, 98, 99, 100, 102, 105, 106, 108, 110, 112, 114, 115, 118, 122, 124, 126, 128, 130, 136, 137, 140, 141, 144, 146, 148, 151, 154, 155, 157, 159, 161, 163, 164, 167, 171, 173, 175, 176, 178, 184, 185, 188, 191, 193, 195, 198, 200, 203, 210, 212, 213, 215, 219, 220, 222, 225, 228, 231, 234, 236, 237}

def g32p_centralizerBound005_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (68, 7)}

theorem g32p_centralizerBound005_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) := by
  decide +kernel

theorem g32p_centralizerBound005_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 5) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound005_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound005_point_block00 t
  · exact g32p_centralizerBound005_point_block01 t
  · exact g32p_centralizerBound005_point_block02 t
  · exact g32p_centralizerBound005_point_block03 t
  · exact g32p_centralizerBound005_point_block04 t
  · exact g32p_centralizerBound005_point_block05 t
  · exact g32p_centralizerBound005_point_block06 t
  · exact g32p_centralizerBound005_point_block07 t
  · exact g32p_centralizerBound005_point_block08 t
  · exact g32p_centralizerBound005_point_block09 t
  · exact g32p_centralizerBound005_point_block10 t
  · exact g32p_centralizerBound005_point_block11 t
  · exact g32p_centralizerBound005_point_block12 t
  · exact g32p_centralizerBound005_point_block13 t
  · exact g32p_centralizerBound005_point_block14 t

theorem g32p_centralizerBound005_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 5) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 5)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound005_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound005_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 5) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 5)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound005_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound005_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 5) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 5)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound005_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound005_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 5) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 5)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound005_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound005_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 5) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 5)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound005_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound005_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 5) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 5) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound005_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 5) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 5)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound005_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound005_stabilizer_block00 t r
  · exact g32p_centralizerBound005_stabilizer_block01 t r
  · exact g32p_centralizerBound005_stabilizer_block02 t r
  · exact g32p_centralizerBound005_stabilizer_block03 t r
  · exact g32p_centralizerBound005_stabilizer_block04 t r

theorem g32p_centralizerBound005_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 5}) ≤ g32p_literalCentralizer 5 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 5 g32p_centralizerBound005_points
    g32p_centralizerBound005_stabilizers ?_ g32p_centralizerBound005_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound005_point_mem i (g32p_centralizer_point_moments 5 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound006_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 28, 32, 33, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 50, 54, 55, 57, 58, 59, 61, 64, 66, 67, 69, 77, 79, 83, 84, 85, 86, 87, 88, 89, 91, 95, 96, 98, 99, 100, 102, 105, 107, 108, 110, 118, 120, 124, 125, 126, 127, 128, 130, 131, 134, 140, 141, 144, 145, 148, 151, 154, 156, 157, 159, 167, 169, 173, 174, 175, 176, 178, 179, 182, 188, 191, 192, 195, 213, 215, 216, 222, 225, 226}

def g32p_centralizerBound006_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7)}

theorem g32p_centralizerBound006_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) := by
  decide +kernel

theorem g32p_centralizerBound006_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 6) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound006_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound006_point_block00 t
  · exact g32p_centralizerBound006_point_block01 t
  · exact g32p_centralizerBound006_point_block02 t
  · exact g32p_centralizerBound006_point_block03 t
  · exact g32p_centralizerBound006_point_block04 t
  · exact g32p_centralizerBound006_point_block05 t
  · exact g32p_centralizerBound006_point_block06 t
  · exact g32p_centralizerBound006_point_block07 t
  · exact g32p_centralizerBound006_point_block08 t
  · exact g32p_centralizerBound006_point_block09 t
  · exact g32p_centralizerBound006_point_block10 t
  · exact g32p_centralizerBound006_point_block11 t
  · exact g32p_centralizerBound006_point_block12 t
  · exact g32p_centralizerBound006_point_block13 t
  · exact g32p_centralizerBound006_point_block14 t

theorem g32p_centralizerBound006_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 6) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 6)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound006_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound006_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 6) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 6)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound006_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound006_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 6) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 6)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound006_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound006_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 6) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 6)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound006_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound006_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 6) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 6)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound006_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound006_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 6) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 6) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound006_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 6) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 6)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound006_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound006_stabilizer_block00 t r
  · exact g32p_centralizerBound006_stabilizer_block01 t r
  · exact g32p_centralizerBound006_stabilizer_block02 t r
  · exact g32p_centralizerBound006_stabilizer_block03 t r
  · exact g32p_centralizerBound006_stabilizer_block04 t r

theorem g32p_centralizerBound006_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 6}) ≤ g32p_literalCentralizer 6 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 6 g32p_centralizerBound006_points
    g32p_centralizerBound006_stabilizers ?_ g32p_centralizerBound006_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound006_point_mem i (g32p_centralizer_point_moments 6 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound007_points : Finset (Fin 240) :=
  {3, 6, 11, 15, 20, 30, 31, 33, 34, 35, 36, 37, 42, 52, 53, 55, 56, 57, 58, 59, 65, 71, 76, 77, 81, 83, 85, 93, 94, 96, 97, 98, 99, 100, 106, 112, 117, 118, 122, 124, 126, 132, 140, 141, 143, 144, 147, 148, 155, 161, 166, 167, 171, 173, 175, 180, 188, 190, 191, 194, 195, 199, 200, 210, 212, 217, 222, 224, 225, 228, 234, 236}

def g32p_centralizerBound007_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound007_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) := by
  decide +kernel

theorem g32p_centralizerBound007_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 7) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound007_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound007_point_block00 t
  · exact g32p_centralizerBound007_point_block01 t
  · exact g32p_centralizerBound007_point_block02 t
  · exact g32p_centralizerBound007_point_block03 t
  · exact g32p_centralizerBound007_point_block04 t
  · exact g32p_centralizerBound007_point_block05 t
  · exact g32p_centralizerBound007_point_block06 t
  · exact g32p_centralizerBound007_point_block07 t
  · exact g32p_centralizerBound007_point_block08 t
  · exact g32p_centralizerBound007_point_block09 t
  · exact g32p_centralizerBound007_point_block10 t
  · exact g32p_centralizerBound007_point_block11 t
  · exact g32p_centralizerBound007_point_block12 t
  · exact g32p_centralizerBound007_point_block13 t
  · exact g32p_centralizerBound007_point_block14 t

theorem g32p_centralizerBound007_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 7) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 7)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound007_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound007_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 7) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 7)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound007_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound007_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 7) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 7)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound007_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound007_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 7) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 7)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound007_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound007_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 7) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 7)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound007_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound007_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 7) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 7) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound007_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 7) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 7)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound007_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound007_stabilizer_block00 t r
  · exact g32p_centralizerBound007_stabilizer_block01 t r
  · exact g32p_centralizerBound007_stabilizer_block02 t r
  · exact g32p_centralizerBound007_stabilizer_block03 t r
  · exact g32p_centralizerBound007_stabilizer_block04 t r

theorem g32p_centralizerBound007_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 7}) ≤ g32p_literalCentralizer 7 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 7 g32p_centralizerBound007_points
    g32p_centralizerBound007_stabilizers ?_ g32p_centralizerBound007_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound007_point_mem i (g32p_centralizer_point_moments 7 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound008_points : Finset (Fin 240) :=
  {3, 6, 9, 11, 15, 18, 20, 26, 27, 30, 31, 33, 34, 35, 36, 37, 40, 42, 48, 49, 52, 53, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 69, 71, 72, 73, 74, 75, 76, 77, 80, 81, 83, 85, 89, 90, 93, 94, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 108, 110, 112, 113, 114, 115, 116, 117, 118, 121, 122, 124, 126, 128, 130, 132, 133, 136, 137, 139, 140, 141, 142, 143, 144, 146, 147, 148, 151, 152, 153, 154, 155, 157, 159, 161, 162, 163, 164, 165, 166, 167, 170, 171, 173, 175, 176, 178, 180, 181, 184, 185, 187, 188, 189, 190, 191, 193, 194, 195, 197, 198, 199, 200, 202, 203, 210, 212, 213, 215, 217, 218, 219, 220, 221, 222, 223, 224, 225, 228, 230, 231, 234, 236, 237}

def g32p_centralizerBound008_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (68, 7)}

theorem g32p_centralizerBound008_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) := by
  decide +kernel

theorem g32p_centralizerBound008_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 8) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound008_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound008_point_block00 t
  · exact g32p_centralizerBound008_point_block01 t
  · exact g32p_centralizerBound008_point_block02 t
  · exact g32p_centralizerBound008_point_block03 t
  · exact g32p_centralizerBound008_point_block04 t
  · exact g32p_centralizerBound008_point_block05 t
  · exact g32p_centralizerBound008_point_block06 t
  · exact g32p_centralizerBound008_point_block07 t
  · exact g32p_centralizerBound008_point_block08 t
  · exact g32p_centralizerBound008_point_block09 t
  · exact g32p_centralizerBound008_point_block10 t
  · exact g32p_centralizerBound008_point_block11 t
  · exact g32p_centralizerBound008_point_block12 t
  · exact g32p_centralizerBound008_point_block13 t
  · exact g32p_centralizerBound008_point_block14 t

theorem g32p_centralizerBound008_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 8) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 8)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound008_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound008_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 8) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 8)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound008_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound008_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 8) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 8)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound008_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound008_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 8) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 8)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound008_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound008_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 8) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 8)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound008_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound008_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 8) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 8) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound008_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 8) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 8)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound008_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound008_stabilizer_block00 t r
  · exact g32p_centralizerBound008_stabilizer_block01 t r
  · exact g32p_centralizerBound008_stabilizer_block02 t r
  · exact g32p_centralizerBound008_stabilizer_block03 t r
  · exact g32p_centralizerBound008_stabilizer_block04 t r

theorem g32p_centralizerBound008_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 8}) ≤ g32p_literalCentralizer 8 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 8 g32p_centralizerBound008_points
    g32p_centralizerBound008_stabilizers ?_ g32p_centralizerBound008_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound008_point_mem i (g32p_centralizer_point_moments 8 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound009_points : Finset (Fin 240) :=
  {3, 6, 12, 13, 15, 21, 22, 31, 32, 33, 34, 36, 43, 44, 53, 54, 55, 56, 58, 76, 79, 84, 85, 94, 95, 96, 97, 99, 117, 120, 125, 126, 132, 140, 143, 144, 145, 147, 166, 169, 174, 175, 180, 188, 190, 191, 192, 194, 199, 217, 222, 224, 225, 226}

def g32p_centralizerBound009_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound009_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) := by
  decide +kernel

theorem g32p_centralizerBound009_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 9) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound009_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound009_point_block00 t
  · exact g32p_centralizerBound009_point_block01 t
  · exact g32p_centralizerBound009_point_block02 t
  · exact g32p_centralizerBound009_point_block03 t
  · exact g32p_centralizerBound009_point_block04 t
  · exact g32p_centralizerBound009_point_block05 t
  · exact g32p_centralizerBound009_point_block06 t
  · exact g32p_centralizerBound009_point_block07 t
  · exact g32p_centralizerBound009_point_block08 t
  · exact g32p_centralizerBound009_point_block09 t
  · exact g32p_centralizerBound009_point_block10 t
  · exact g32p_centralizerBound009_point_block11 t
  · exact g32p_centralizerBound009_point_block12 t
  · exact g32p_centralizerBound009_point_block13 t
  · exact g32p_centralizerBound009_point_block14 t

theorem g32p_centralizerBound009_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 9) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 9)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound009_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound009_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 9) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 9)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound009_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound009_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 9) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 9)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound009_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound009_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 9) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 9)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound009_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound009_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 9) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 9)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound009_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound009_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 9) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 9) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound009_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 9) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 9)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound009_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound009_stabilizer_block00 t r
  · exact g32p_centralizerBound009_stabilizer_block01 t r
  · exact g32p_centralizerBound009_stabilizer_block02 t r
  · exact g32p_centralizerBound009_stabilizer_block03 t r
  · exact g32p_centralizerBound009_stabilizer_block04 t r

theorem g32p_centralizerBound009_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 9}) ≤ g32p_literalCentralizer 9 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 9 g32p_centralizerBound009_points
    g32p_centralizerBound009_stabilizers ?_ g32p_centralizerBound009_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound009_point_mem i (g32p_centralizer_point_moments 9 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound010_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 11, 14, 15, 16, 20, 25, 27, 31, 36, 38, 42, 47, 49, 53, 58, 62, 66, 76, 83, 88, 90, 94, 99, 103, 107, 117, 124, 152, 156, 166, 173}

def g32p_centralizerBound010_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (68, 7)}

theorem g32p_centralizerBound010_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) := by
  decide +kernel

theorem g32p_centralizerBound010_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 10) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound010_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound010_point_block00 t
  · exact g32p_centralizerBound010_point_block01 t
  · exact g32p_centralizerBound010_point_block02 t
  · exact g32p_centralizerBound010_point_block03 t
  · exact g32p_centralizerBound010_point_block04 t
  · exact g32p_centralizerBound010_point_block05 t
  · exact g32p_centralizerBound010_point_block06 t
  · exact g32p_centralizerBound010_point_block07 t
  · exact g32p_centralizerBound010_point_block08 t
  · exact g32p_centralizerBound010_point_block09 t
  · exact g32p_centralizerBound010_point_block10 t
  · exact g32p_centralizerBound010_point_block11 t
  · exact g32p_centralizerBound010_point_block12 t
  · exact g32p_centralizerBound010_point_block13 t
  · exact g32p_centralizerBound010_point_block14 t

theorem g32p_centralizerBound010_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 10) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 10)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound010_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound010_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 10) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 10)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound010_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound010_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 10) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 10)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound010_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound010_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 10) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 10)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound010_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound010_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 10) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 10)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound010_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound010_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 10) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 10) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound010_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 10) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 10)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound010_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound010_stabilizer_block00 t r
  · exact g32p_centralizerBound010_stabilizer_block01 t r
  · exact g32p_centralizerBound010_stabilizer_block02 t r
  · exact g32p_centralizerBound010_stabilizer_block03 t r
  · exact g32p_centralizerBound010_stabilizer_block04 t r

theorem g32p_centralizerBound010_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 10}) ≤ g32p_literalCentralizer 10 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 10 g32p_centralizerBound010_points
    g32p_centralizerBound010_stabilizers ?_ g32p_centralizerBound010_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound010_point_mem i (g32p_centralizer_point_moments 10 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound011_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 28, 32, 33, 35, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 50, 54, 55, 57, 58, 59, 61, 64, 66, 67, 69, 77, 79, 83, 84, 85, 86, 87, 88, 89, 91, 95, 96, 98, 99, 100, 102, 105, 107, 108, 110, 118, 120, 124, 125, 126, 127, 128, 130, 131, 134, 140, 141, 144, 145, 148, 151, 154, 156, 157, 159, 167, 169, 173, 174, 175, 176, 178, 179, 182, 188, 191, 192, 195, 213, 215, 216, 222, 225, 226}

def g32p_centralizerBound011_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (26, 1), (26, 2), (26, 8)}

theorem g32p_centralizerBound011_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) := by
  decide +kernel

theorem g32p_centralizerBound011_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 11) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound011_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound011_point_block00 t
  · exact g32p_centralizerBound011_point_block01 t
  · exact g32p_centralizerBound011_point_block02 t
  · exact g32p_centralizerBound011_point_block03 t
  · exact g32p_centralizerBound011_point_block04 t
  · exact g32p_centralizerBound011_point_block05 t
  · exact g32p_centralizerBound011_point_block06 t
  · exact g32p_centralizerBound011_point_block07 t
  · exact g32p_centralizerBound011_point_block08 t
  · exact g32p_centralizerBound011_point_block09 t
  · exact g32p_centralizerBound011_point_block10 t
  · exact g32p_centralizerBound011_point_block11 t
  · exact g32p_centralizerBound011_point_block12 t
  · exact g32p_centralizerBound011_point_block13 t
  · exact g32p_centralizerBound011_point_block14 t

theorem g32p_centralizerBound011_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 11) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 11)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound011_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound011_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 11) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 11)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound011_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound011_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 11) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 11)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound011_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound011_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 11) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 11)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound011_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound011_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 11) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 11)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound011_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound011_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 11) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 11) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound011_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 11) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 11)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound011_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound011_stabilizer_block00 t r
  · exact g32p_centralizerBound011_stabilizer_block01 t r
  · exact g32p_centralizerBound011_stabilizer_block02 t r
  · exact g32p_centralizerBound011_stabilizer_block03 t r
  · exact g32p_centralizerBound011_stabilizer_block04 t r

theorem g32p_centralizerBound011_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 11}) ≤ g32p_literalCentralizer 11 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 11 g32p_centralizerBound011_points
    g32p_centralizerBound011_stabilizers ?_ g32p_centralizerBound011_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound011_point_mem i (g32p_centralizer_point_moments 11 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound012_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 12, 14, 15, 21, 25, 26, 27, 28, 36, 43, 47, 48, 49, 50, 58, 61, 62, 79, 84, 88, 89, 90, 91, 99, 102, 103, 120, 125, 127, 132, 133, 134, 142, 143, 145, 151, 152, 169, 174, 180, 181, 182, 189, 190, 192, 217, 218, 223, 224, 226}

def g32p_centralizerBound012_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound012_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) := by
  decide +kernel

theorem g32p_centralizerBound012_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 12) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound012_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound012_point_block00 t
  · exact g32p_centralizerBound012_point_block01 t
  · exact g32p_centralizerBound012_point_block02 t
  · exact g32p_centralizerBound012_point_block03 t
  · exact g32p_centralizerBound012_point_block04 t
  · exact g32p_centralizerBound012_point_block05 t
  · exact g32p_centralizerBound012_point_block06 t
  · exact g32p_centralizerBound012_point_block07 t
  · exact g32p_centralizerBound012_point_block08 t
  · exact g32p_centralizerBound012_point_block09 t
  · exact g32p_centralizerBound012_point_block10 t
  · exact g32p_centralizerBound012_point_block11 t
  · exact g32p_centralizerBound012_point_block12 t
  · exact g32p_centralizerBound012_point_block13 t
  · exact g32p_centralizerBound012_point_block14 t

theorem g32p_centralizerBound012_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 12) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 12)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound012_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound012_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 12) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 12)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound012_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound012_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 12) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 12)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound012_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound012_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 12) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 12)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound012_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound012_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 12) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 12)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound012_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound012_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 12) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 12) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound012_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 12) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 12)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound012_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound012_stabilizer_block00 t r
  · exact g32p_centralizerBound012_stabilizer_block01 t r
  · exact g32p_centralizerBound012_stabilizer_block02 t r
  · exact g32p_centralizerBound012_stabilizer_block03 t r
  · exact g32p_centralizerBound012_stabilizer_block04 t r

theorem g32p_centralizerBound012_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 12}) ≤ g32p_literalCentralizer 12 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 12 g32p_centralizerBound012_points
    g32p_centralizerBound012_stabilizers ?_ g32p_centralizerBound012_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound012_point_mem i (g32p_centralizer_point_moments 12 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound013_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 14, 15, 24, 25, 26, 27, 28, 29, 31, 33, 34, 35, 36, 37, 46, 47, 48, 49, 50, 51, 53, 55, 56, 57, 58, 59, 61, 62, 65, 73, 76, 77, 78, 81, 87, 88, 89, 90, 91, 92, 94, 96, 97, 98, 99, 100, 102, 103, 106, 114, 117, 118, 119, 122, 127, 131, 134, 135, 141, 144, 147, 148, 151, 152, 155, 163, 166, 167, 168, 171, 179, 182, 183, 191, 194, 195, 199, 200, 203, 204, 205, 209, 210, 212, 216, 225, 228, 231, 233, 234, 236, 237}

def g32p_centralizerBound013_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (19, 8), (48, 5)}

theorem g32p_centralizerBound013_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) := by
  decide +kernel

theorem g32p_centralizerBound013_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 13) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound013_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound013_point_block00 t
  · exact g32p_centralizerBound013_point_block01 t
  · exact g32p_centralizerBound013_point_block02 t
  · exact g32p_centralizerBound013_point_block03 t
  · exact g32p_centralizerBound013_point_block04 t
  · exact g32p_centralizerBound013_point_block05 t
  · exact g32p_centralizerBound013_point_block06 t
  · exact g32p_centralizerBound013_point_block07 t
  · exact g32p_centralizerBound013_point_block08 t
  · exact g32p_centralizerBound013_point_block09 t
  · exact g32p_centralizerBound013_point_block10 t
  · exact g32p_centralizerBound013_point_block11 t
  · exact g32p_centralizerBound013_point_block12 t
  · exact g32p_centralizerBound013_point_block13 t
  · exact g32p_centralizerBound013_point_block14 t

theorem g32p_centralizerBound013_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 13) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 13)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound013_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound013_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 13) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 13)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound013_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound013_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 13) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 13)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound013_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound013_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 13) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 13)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound013_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound013_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 13) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 13)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound013_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound013_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 13) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 13) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound013_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 13) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 13)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound013_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound013_stabilizer_block00 t r
  · exact g32p_centralizerBound013_stabilizer_block01 t r
  · exact g32p_centralizerBound013_stabilizer_block02 t r
  · exact g32p_centralizerBound013_stabilizer_block03 t r
  · exact g32p_centralizerBound013_stabilizer_block04 t r

theorem g32p_centralizerBound013_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 13}) ≤ g32p_literalCentralizer 13 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 13 g32p_centralizerBound013_points
    g32p_centralizerBound013_stabilizers ?_ g32p_centralizerBound013_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound013_point_mem i (g32p_centralizer_point_moments 13 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound014_points : Finset (Fin 240) :=
  {3, 6, 10, 12, 13, 15, 19, 21, 22, 32, 33, 36, 41, 43, 44, 54, 55, 58, 68, 78, 79, 84, 85, 95, 96, 99, 109, 119, 120, 125, 126, 138, 140, 144, 145, 149, 158, 168, 169, 174, 175, 186, 188, 191, 192, 196, 204, 206, 209, 222, 225, 226, 227, 233}

def g32p_centralizerBound014_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound014_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) := by
  decide +kernel

theorem g32p_centralizerBound014_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 14) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound014_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound014_point_block00 t
  · exact g32p_centralizerBound014_point_block01 t
  · exact g32p_centralizerBound014_point_block02 t
  · exact g32p_centralizerBound014_point_block03 t
  · exact g32p_centralizerBound014_point_block04 t
  · exact g32p_centralizerBound014_point_block05 t
  · exact g32p_centralizerBound014_point_block06 t
  · exact g32p_centralizerBound014_point_block07 t
  · exact g32p_centralizerBound014_point_block08 t
  · exact g32p_centralizerBound014_point_block09 t
  · exact g32p_centralizerBound014_point_block10 t
  · exact g32p_centralizerBound014_point_block11 t
  · exact g32p_centralizerBound014_point_block12 t
  · exact g32p_centralizerBound014_point_block13 t
  · exact g32p_centralizerBound014_point_block14 t

theorem g32p_centralizerBound014_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 14) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 14)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound014_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound014_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 14) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 14)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound014_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound014_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 14) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 14)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound014_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound014_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 14) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 14)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound014_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound014_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 14) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 14)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound014_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound014_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 14) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 14) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound014_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 14) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 14)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound014_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound014_stabilizer_block00 t r
  · exact g32p_centralizerBound014_stabilizer_block01 t r
  · exact g32p_centralizerBound014_stabilizer_block02 t r
  · exact g32p_centralizerBound014_stabilizer_block03 t r
  · exact g32p_centralizerBound014_stabilizer_block04 t r

theorem g32p_centralizerBound014_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 14}) ≤ g32p_literalCentralizer 14 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 14 g32p_centralizerBound014_points
    g32p_centralizerBound014_stabilizers ?_ g32p_centralizerBound014_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound014_point_mem i (g32p_centralizer_point_moments 14 x i hi.symm)

end HodgeLean.Foundations.Program

end
end

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound015_points : Finset (Fin 240) :=
  {3, 6, 11, 15, 20, 27, 30, 31, 33, 34, 35, 36, 37, 42, 49, 52, 53, 55, 56, 57, 58, 59, 62, 65, 71, 73, 74, 75, 76, 77, 81, 83, 85, 90, 93, 94, 96, 97, 98, 99, 100, 103, 106, 112, 114, 115, 116, 117, 118, 122, 124, 126, 132, 133, 136, 137, 139, 140, 141, 142, 143, 144, 146, 147, 148, 152, 155, 161, 163, 164, 165, 166, 167, 171, 173, 175, 180, 181, 184, 185, 187, 188, 189, 190, 191, 193, 194, 195, 198, 199, 200, 203, 210, 212, 217, 218, 219, 220, 221, 222, 223, 224, 225, 228, 231, 234, 236, 237}

def g32p_centralizerBound015_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound015_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) := by
  decide +kernel

theorem g32p_centralizerBound015_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 15) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound015_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound015_point_block00 t
  · exact g32p_centralizerBound015_point_block01 t
  · exact g32p_centralizerBound015_point_block02 t
  · exact g32p_centralizerBound015_point_block03 t
  · exact g32p_centralizerBound015_point_block04 t
  · exact g32p_centralizerBound015_point_block05 t
  · exact g32p_centralizerBound015_point_block06 t
  · exact g32p_centralizerBound015_point_block07 t
  · exact g32p_centralizerBound015_point_block08 t
  · exact g32p_centralizerBound015_point_block09 t
  · exact g32p_centralizerBound015_point_block10 t
  · exact g32p_centralizerBound015_point_block11 t
  · exact g32p_centralizerBound015_point_block12 t
  · exact g32p_centralizerBound015_point_block13 t
  · exact g32p_centralizerBound015_point_block14 t

theorem g32p_centralizerBound015_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 15) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 15)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound015_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound015_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 15) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 15)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound015_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound015_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 15) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 15)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound015_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound015_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 15) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 15)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound015_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound015_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 15) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 15)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound015_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound015_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 15) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 15) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound015_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 15) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 15)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound015_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound015_stabilizer_block00 t r
  · exact g32p_centralizerBound015_stabilizer_block01 t r
  · exact g32p_centralizerBound015_stabilizer_block02 t r
  · exact g32p_centralizerBound015_stabilizer_block03 t r
  · exact g32p_centralizerBound015_stabilizer_block04 t r

theorem g32p_centralizerBound015_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 15}) ≤ g32p_literalCentralizer 15 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 15 g32p_centralizerBound015_points
    g32p_centralizerBound015_stabilizers ?_ g32p_centralizerBound015_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound015_point_mem i (g32p_centralizer_point_moments 15 x i hi.symm)

end HodgeLean.Foundations.Program

end
end
