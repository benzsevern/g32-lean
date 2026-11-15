import HodgeLean.Foundations.Program.G32PropFourSixPacked0201
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound081_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 99, 133, 138, 142, 149, 181, 186, 189, 196, 206, 218, 223, 227}

def g32p_centralizerBound081_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (7, 8), (10, 5), (12, 7), (14, 5), (15, 7), (19, 0), (23, 4), (27, 4), (32, 4), (33, 6), (36, 1), (37, 2), (39, 2), (41, 6), (48, 6), (50, 2), (52, 6), (60, 5), (62, 2), (63, 7), (66, 0), (71, 1)}

theorem g32p_centralizerBound081_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) := by
  decide +kernel

theorem g32p_centralizerBound081_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 81) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound081_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound081_point_block00 t
  · exact g32p_centralizerBound081_point_block01 t
  · exact g32p_centralizerBound081_point_block02 t
  · exact g32p_centralizerBound081_point_block03 t
  · exact g32p_centralizerBound081_point_block04 t
  · exact g32p_centralizerBound081_point_block05 t
  · exact g32p_centralizerBound081_point_block06 t
  · exact g32p_centralizerBound081_point_block07 t
  · exact g32p_centralizerBound081_point_block08 t
  · exact g32p_centralizerBound081_point_block09 t
  · exact g32p_centralizerBound081_point_block10 t
  · exact g32p_centralizerBound081_point_block11 t
  · exact g32p_centralizerBound081_point_block12 t
  · exact g32p_centralizerBound081_point_block13 t
  · exact g32p_centralizerBound081_point_block14 t

theorem g32p_centralizerBound081_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 81) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 81)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound081_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound081_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 81) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 81)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound081_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound081_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 81) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 81)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound081_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound081_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 81) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 81)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound081_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound081_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 81) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 81)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound081_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound081_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 81) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 81) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound081_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 81) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 81)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound081_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound081_stabilizer_block00 t r
  · exact g32p_centralizerBound081_stabilizer_block01 t r
  · exact g32p_centralizerBound081_stabilizer_block02 t r
  · exact g32p_centralizerBound081_stabilizer_block03 t r
  · exact g32p_centralizerBound081_stabilizer_block04 t r

theorem g32p_centralizerBound081_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 81}) ≤ g32p_literalCentralizer 81 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 81 g32p_centralizerBound081_points
    g32p_centralizerBound081_stabilizers ?_ g32p_centralizerBound081_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound081_point_mem i (g32p_centralizer_point_moments 81 x i hi.symm)

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

def g32p_centralizerBound082_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 8, 10, 11, 12, 14, 15, 17, 19, 20, 21, 23, 24, 25, 26, 27, 28, 29, 33, 34, 36, 37, 39, 41, 42, 43, 45, 46, 47, 48, 49, 50, 51, 55, 56, 58, 59, 60, 61, 62, 63, 64, 65, 68, 69, 70, 72, 73, 74, 75, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 96, 97, 99, 100, 101, 102, 103, 104, 105, 106, 109, 110, 111, 113, 114, 115, 116, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 137, 138, 139, 140, 142, 143, 144, 145, 147, 149, 150, 151, 152, 153, 154, 155, 158, 159, 160, 162, 163, 164, 165, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 185, 186, 187, 188, 189, 190, 191, 192, 194, 196, 197, 199, 200, 202, 203, 204, 205, 206, 207, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 233, 234, 235, 236, 237}

def g32p_centralizerBound082_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (14, 5), (18, 2), (21, 8), (32, 4), (34, 7), (42, 8), (54, 8), (68, 7)}

theorem g32p_centralizerBound082_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) := by
  decide +kernel

theorem g32p_centralizerBound082_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 82) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound082_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound082_point_block00 t
  · exact g32p_centralizerBound082_point_block01 t
  · exact g32p_centralizerBound082_point_block02 t
  · exact g32p_centralizerBound082_point_block03 t
  · exact g32p_centralizerBound082_point_block04 t
  · exact g32p_centralizerBound082_point_block05 t
  · exact g32p_centralizerBound082_point_block06 t
  · exact g32p_centralizerBound082_point_block07 t
  · exact g32p_centralizerBound082_point_block08 t
  · exact g32p_centralizerBound082_point_block09 t
  · exact g32p_centralizerBound082_point_block10 t
  · exact g32p_centralizerBound082_point_block11 t
  · exact g32p_centralizerBound082_point_block12 t
  · exact g32p_centralizerBound082_point_block13 t
  · exact g32p_centralizerBound082_point_block14 t

theorem g32p_centralizerBound082_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 82) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 82)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound082_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound082_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 82) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 82)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound082_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound082_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 82) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 82)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound082_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound082_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 82) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 82)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound082_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound082_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 82) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 82)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound082_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound082_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 82) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 82) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound082_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 82) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 82)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound082_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound082_stabilizer_block00 t r
  · exact g32p_centralizerBound082_stabilizer_block01 t r
  · exact g32p_centralizerBound082_stabilizer_block02 t r
  · exact g32p_centralizerBound082_stabilizer_block03 t r
  · exact g32p_centralizerBound082_stabilizer_block04 t r

theorem g32p_centralizerBound082_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 82}) ≤ g32p_literalCentralizer 82 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 82 g32p_centralizerBound082_points
    g32p_centralizerBound082_stabilizers ?_ g32p_centralizerBound082_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound082_point_mem i (g32p_centralizer_point_moments 82 x i hi.symm)

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

def g32p_centralizerBound083_points : Finset (Fin 240) :=
  {0, 1, 3, 4, 6, 9, 10, 12, 15, 18, 19, 21, 24, 29, 36, 37, 40, 41, 43, 46, 51, 58, 59, 60, 64, 65, 67, 68, 74, 75, 77, 81, 82, 84, 85, 87, 92, 99, 100, 101, 105, 106, 108, 109, 115, 116, 118, 122, 123, 125, 126, 130, 131, 135, 137, 139, 140, 150, 154, 155, 157, 158, 164, 165, 167, 171, 172, 174, 175, 178, 179, 183, 185, 187, 188, 200, 201, 205, 207, 208, 210, 211, 212, 215, 216, 220, 221, 222, 228, 229, 232, 234, 235, 236, 238, 239}

def g32p_centralizerBound083_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (14, 5), (32, 4)}

theorem g32p_centralizerBound083_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) := by
  decide +kernel

theorem g32p_centralizerBound083_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 83) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound083_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound083_point_block00 t
  · exact g32p_centralizerBound083_point_block01 t
  · exact g32p_centralizerBound083_point_block02 t
  · exact g32p_centralizerBound083_point_block03 t
  · exact g32p_centralizerBound083_point_block04 t
  · exact g32p_centralizerBound083_point_block05 t
  · exact g32p_centralizerBound083_point_block06 t
  · exact g32p_centralizerBound083_point_block07 t
  · exact g32p_centralizerBound083_point_block08 t
  · exact g32p_centralizerBound083_point_block09 t
  · exact g32p_centralizerBound083_point_block10 t
  · exact g32p_centralizerBound083_point_block11 t
  · exact g32p_centralizerBound083_point_block12 t
  · exact g32p_centralizerBound083_point_block13 t
  · exact g32p_centralizerBound083_point_block14 t

theorem g32p_centralizerBound083_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 83) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 83)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound083_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound083_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 83) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 83)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound083_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound083_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 83) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 83)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound083_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound083_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 83) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 83)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound083_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound083_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 83) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 83)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound083_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound083_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 83) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 83) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound083_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 83) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 83)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound083_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound083_stabilizer_block00 t r
  · exact g32p_centralizerBound083_stabilizer_block01 t r
  · exact g32p_centralizerBound083_stabilizer_block02 t r
  · exact g32p_centralizerBound083_stabilizer_block03 t r
  · exact g32p_centralizerBound083_stabilizer_block04 t r

theorem g32p_centralizerBound083_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 83}) ≤ g32p_literalCentralizer 83 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 83 g32p_centralizerBound083_points
    g32p_centralizerBound083_stabilizers ?_ g32p_centralizerBound083_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound083_point_mem i (g32p_centralizer_point_moments 83 x i hi.symm)

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

def g32p_centralizerBound084_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 99}

def g32p_centralizerBound084_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (2, 7), (3, 4), (4, 5), (5, 4), (6, 1), (7, 0), (8, 8), (9, 0), (12, 0), (14, 5), (16, 7), (18, 2), (19, 6), (21, 8), (22, 7), (23, 6), (24, 2), (25, 7), (26, 2), (27, 0), (28, 4), (29, 5), (30, 4), (31, 1), (32, 4), (33, 3), (34, 7), (36, 5), (37, 3), (38, 1), (42, 8), (45, 1), (46, 7), (47, 0), (50, 0), (52, 5), (53, 8), (54, 8), (55, 4), (56, 2), (59, 5), (60, 2), (61, 5), (62, 4), (63, 3), (64, 1), (65, 7), (66, 6), (67, 2), (68, 7), (69, 2), (70, 0), (71, 3)}

theorem g32p_centralizerBound084_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) := by
  decide +kernel

theorem g32p_centralizerBound084_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 84) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound084_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound084_point_block00 t
  · exact g32p_centralizerBound084_point_block01 t
  · exact g32p_centralizerBound084_point_block02 t
  · exact g32p_centralizerBound084_point_block03 t
  · exact g32p_centralizerBound084_point_block04 t
  · exact g32p_centralizerBound084_point_block05 t
  · exact g32p_centralizerBound084_point_block06 t
  · exact g32p_centralizerBound084_point_block07 t
  · exact g32p_centralizerBound084_point_block08 t
  · exact g32p_centralizerBound084_point_block09 t
  · exact g32p_centralizerBound084_point_block10 t
  · exact g32p_centralizerBound084_point_block11 t
  · exact g32p_centralizerBound084_point_block12 t
  · exact g32p_centralizerBound084_point_block13 t
  · exact g32p_centralizerBound084_point_block14 t

theorem g32p_centralizerBound084_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 84) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 84)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound084_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound084_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 84) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 84)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound084_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound084_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 84) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 84)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound084_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound084_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 84) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 84)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound084_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound084_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 84) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 84)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound084_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound084_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 84) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 84) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound084_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 84) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 84)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound084_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound084_stabilizer_block00 t r
  · exact g32p_centralizerBound084_stabilizer_block01 t r
  · exact g32p_centralizerBound084_stabilizer_block02 t r
  · exact g32p_centralizerBound084_stabilizer_block03 t r
  · exact g32p_centralizerBound084_stabilizer_block04 t r

theorem g32p_centralizerBound084_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 84}) ≤ g32p_literalCentralizer 84 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 84 g32p_centralizerBound084_points
    g32p_centralizerBound084_stabilizers ?_ g32p_centralizerBound084_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound084_point_mem i (g32p_centralizer_point_moments 84 x i hi.symm)

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

def g32p_centralizerBound085_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 14, 15, 16, 20, 21, 25, 26, 27, 28, 30, 31, 36, 37, 38, 42, 43, 47, 48, 49, 50, 52, 53, 58, 59, 60, 61, 62, 63, 66, 69, 70, 71, 73, 74, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 88, 89, 90, 91, 93, 94, 99, 100, 101, 102, 103, 104, 107, 110, 111, 112, 114, 115, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 132, 133, 134, 137, 140, 142, 143, 145, 150, 151, 152, 153, 156, 159, 160, 161, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 180, 181, 182, 185, 188, 189, 190, 192, 203, 204, 207, 209, 210, 211, 213, 214, 217, 218, 220, 222, 223, 224, 226, 231, 233, 234, 235, 236, 237}

def g32p_centralizerBound085_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (10, 5), (60, 5)}

theorem g32p_centralizerBound085_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) := by
  decide +kernel

theorem g32p_centralizerBound085_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 85) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound085_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound085_point_block00 t
  · exact g32p_centralizerBound085_point_block01 t
  · exact g32p_centralizerBound085_point_block02 t
  · exact g32p_centralizerBound085_point_block03 t
  · exact g32p_centralizerBound085_point_block04 t
  · exact g32p_centralizerBound085_point_block05 t
  · exact g32p_centralizerBound085_point_block06 t
  · exact g32p_centralizerBound085_point_block07 t
  · exact g32p_centralizerBound085_point_block08 t
  · exact g32p_centralizerBound085_point_block09 t
  · exact g32p_centralizerBound085_point_block10 t
  · exact g32p_centralizerBound085_point_block11 t
  · exact g32p_centralizerBound085_point_block12 t
  · exact g32p_centralizerBound085_point_block13 t
  · exact g32p_centralizerBound085_point_block14 t

theorem g32p_centralizerBound085_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 85) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 85)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound085_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound085_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 85) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 85)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound085_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound085_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 85) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 85)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound085_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound085_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 85) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 85)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound085_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound085_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 85) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 85)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound085_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound085_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 85) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 85) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound085_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 85) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 85)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound085_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound085_stabilizer_block00 t r
  · exact g32p_centralizerBound085_stabilizer_block01 t r
  · exact g32p_centralizerBound085_stabilizer_block02 t r
  · exact g32p_centralizerBound085_stabilizer_block03 t r
  · exact g32p_centralizerBound085_stabilizer_block04 t r

theorem g32p_centralizerBound085_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 85}) ≤ g32p_literalCentralizer 85 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 85 g32p_centralizerBound085_points
    g32p_centralizerBound085_stabilizers ?_ g32p_centralizerBound085_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound085_point_mem i (g32p_centralizer_point_moments 85 x i hi.symm)

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

def g32p_centralizerBound086_points : Finset (Fin 240) :=
  {3, 6, 15, 33, 36, 55, 58, 82, 96, 99, 123, 144, 172, 191, 207, 211, 225, 235}

def g32p_centralizerBound086_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 5), (20, 3), (26, 2), (53, 1), (70, 6)}

theorem g32p_centralizerBound086_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) := by
  decide +kernel

theorem g32p_centralizerBound086_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 86) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound086_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound086_point_block00 t
  · exact g32p_centralizerBound086_point_block01 t
  · exact g32p_centralizerBound086_point_block02 t
  · exact g32p_centralizerBound086_point_block03 t
  · exact g32p_centralizerBound086_point_block04 t
  · exact g32p_centralizerBound086_point_block05 t
  · exact g32p_centralizerBound086_point_block06 t
  · exact g32p_centralizerBound086_point_block07 t
  · exact g32p_centralizerBound086_point_block08 t
  · exact g32p_centralizerBound086_point_block09 t
  · exact g32p_centralizerBound086_point_block10 t
  · exact g32p_centralizerBound086_point_block11 t
  · exact g32p_centralizerBound086_point_block12 t
  · exact g32p_centralizerBound086_point_block13 t
  · exact g32p_centralizerBound086_point_block14 t

theorem g32p_centralizerBound086_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 86) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 86)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound086_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound086_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 86) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 86)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound086_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound086_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 86) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 86)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound086_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound086_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 86) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 86)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound086_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound086_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 86) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 86)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound086_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound086_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 86) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 86) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound086_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 86) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 86)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound086_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound086_stabilizer_block00 t r
  · exact g32p_centralizerBound086_stabilizer_block01 t r
  · exact g32p_centralizerBound086_stabilizer_block02 t r
  · exact g32p_centralizerBound086_stabilizer_block03 t r
  · exact g32p_centralizerBound086_stabilizer_block04 t r

theorem g32p_centralizerBound086_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 86}) ≤ g32p_literalCentralizer 86 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 86 g32p_centralizerBound086_points
    g32p_centralizerBound086_stabilizers ?_ g32p_centralizerBound086_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound086_point_mem i (g32p_centralizer_point_moments 86 x i hi.symm)

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

def g32p_centralizerBound087_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 11, 13, 14, 15, 16, 17, 20, 22, 23, 25, 27, 28, 29, 31, 32, 34, 35, 36, 38, 39, 42, 44, 45, 47, 49, 50, 51, 53, 54, 56, 57, 58, 62, 63, 64, 65, 66, 69, 72, 73, 76, 78, 79, 80, 81, 82, 83, 85, 86, 88, 90, 91, 92, 94, 95, 97, 98, 99, 103, 104, 105, 106, 107, 110, 113, 114, 117, 119, 120, 121, 122, 123, 124, 126, 127, 128, 130, 133, 134, 135, 136, 138, 140, 141, 142, 145, 146, 147, 148, 149, 152, 153, 154, 155, 156, 159, 162, 163, 166, 168, 169, 170, 171, 172, 173, 175, 176, 178, 181, 182, 183, 184, 186, 188, 189, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 215, 218, 219, 222, 223, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239}

def g32p_centralizerBound087_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 2), (0, 5), (14, 0), (14, 2), (14, 5), (16, 0), (16, 2), (16, 5), (20, 3), (20, 6), (20, 8), (32, 1), (32, 4), (32, 7), (49, 1), (49, 4), (49, 7), (64, 0), (64, 2), (64, 5), (70, 3), (70, 6), (70, 8)}

theorem g32p_centralizerBound087_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) := by
  decide +kernel

theorem g32p_centralizerBound087_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 87) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound087_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound087_point_block00 t
  · exact g32p_centralizerBound087_point_block01 t
  · exact g32p_centralizerBound087_point_block02 t
  · exact g32p_centralizerBound087_point_block03 t
  · exact g32p_centralizerBound087_point_block04 t
  · exact g32p_centralizerBound087_point_block05 t
  · exact g32p_centralizerBound087_point_block06 t
  · exact g32p_centralizerBound087_point_block07 t
  · exact g32p_centralizerBound087_point_block08 t
  · exact g32p_centralizerBound087_point_block09 t
  · exact g32p_centralizerBound087_point_block10 t
  · exact g32p_centralizerBound087_point_block11 t
  · exact g32p_centralizerBound087_point_block12 t
  · exact g32p_centralizerBound087_point_block13 t
  · exact g32p_centralizerBound087_point_block14 t

theorem g32p_centralizerBound087_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 87) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 87)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound087_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound087_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 87) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 87)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound087_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound087_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 87) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 87)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound087_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound087_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 87) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 87)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound087_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound087_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 87) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 87)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound087_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound087_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 87) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 87) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound087_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 87) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 87)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound087_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound087_stabilizer_block00 t r
  · exact g32p_centralizerBound087_stabilizer_block01 t r
  · exact g32p_centralizerBound087_stabilizer_block02 t r
  · exact g32p_centralizerBound087_stabilizer_block03 t r
  · exact g32p_centralizerBound087_stabilizer_block04 t r

theorem g32p_centralizerBound087_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 87}) ≤ g32p_literalCentralizer 87 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 87 g32p_centralizerBound087_points
    g32p_centralizerBound087_stabilizers ?_ g32p_centralizerBound087_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound087_point_mem i (g32p_centralizer_point_moments 87 x i hi.symm)

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

def g32p_centralizerBound088_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 23, 24, 25, 27, 29, 34, 36, 37, 39, 40, 41, 42, 43, 45, 46, 47, 49, 51, 56, 58, 59, 60, 62, 63, 64, 65, 67, 68, 69, 74, 75, 77, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 90, 92, 97, 99, 100, 101, 103, 104, 105, 106, 108, 109, 110, 115, 116, 118, 120, 121, 122, 123, 124, 125, 126, 128, 130, 131, 132, 135, 136, 137, 138, 139, 140, 143, 145, 146, 147, 149, 150, 152, 153, 154, 155, 157, 158, 159, 164, 165, 167, 169, 170, 171, 172, 173, 174, 175, 176, 178, 179, 180, 183, 184, 185, 186, 187, 188, 190, 192, 193, 194, 196, 198, 199, 200, 201, 205, 206, 207, 208, 210, 211, 212, 213, 215, 216, 217, 219, 220, 221, 222, 224, 226, 227, 228, 229, 232, 234, 235, 236, 238, 239}

def g32p_centralizerBound088_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (13, 3), (13, 4), (13, 5), (14, 3), (14, 4), (14, 5), (32, 3), (32, 4), (32, 5), (43, 1), (43, 2), (43, 8), (55, 1), (55, 2), (55, 8), (59, 1), (59, 2), (59, 8), (69, 0), (69, 6), (69, 7)}

theorem g32p_centralizerBound088_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) := by
  decide +kernel

theorem g32p_centralizerBound088_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 88) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound088_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound088_point_block00 t
  · exact g32p_centralizerBound088_point_block01 t
  · exact g32p_centralizerBound088_point_block02 t
  · exact g32p_centralizerBound088_point_block03 t
  · exact g32p_centralizerBound088_point_block04 t
  · exact g32p_centralizerBound088_point_block05 t
  · exact g32p_centralizerBound088_point_block06 t
  · exact g32p_centralizerBound088_point_block07 t
  · exact g32p_centralizerBound088_point_block08 t
  · exact g32p_centralizerBound088_point_block09 t
  · exact g32p_centralizerBound088_point_block10 t
  · exact g32p_centralizerBound088_point_block11 t
  · exact g32p_centralizerBound088_point_block12 t
  · exact g32p_centralizerBound088_point_block13 t
  · exact g32p_centralizerBound088_point_block14 t

theorem g32p_centralizerBound088_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 88) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 88)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound088_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound088_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 88) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 88)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound088_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound088_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 88) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 88)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound088_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound088_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 88) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 88)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound088_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound088_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 88) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 88)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound088_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound088_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 88) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 88) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound088_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 88) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 88)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound088_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound088_stabilizer_block00 t r
  · exact g32p_centralizerBound088_stabilizer_block01 t r
  · exact g32p_centralizerBound088_stabilizer_block02 t r
  · exact g32p_centralizerBound088_stabilizer_block03 t r
  · exact g32p_centralizerBound088_stabilizer_block04 t r

theorem g32p_centralizerBound088_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 88}) ≤ g32p_literalCentralizer 88 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 88 g32p_centralizerBound088_points
    g32p_centralizerBound088_stabilizers ?_ g32p_centralizerBound088_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound088_point_mem i (g32p_centralizer_point_moments 88 x i hi.symm)

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

def g32p_centralizerBound089_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 14, 15, 17, 18, 19, 20, 21, 23, 25, 26, 27, 28, 33, 34, 35, 36, 39, 40, 41, 42, 43, 45, 47, 48, 49, 50, 55, 56, 57, 58, 60, 61, 62, 65, 67, 68, 69, 70, 72, 78, 79, 81, 83, 84, 86, 88, 89, 90, 91, 96, 97, 98, 99, 101, 102, 103, 106, 108, 109, 110, 111, 113, 119, 120, 122, 124, 125, 127, 128, 129, 132, 133, 134, 141, 142, 143, 144, 145, 147, 148, 150, 151, 152, 155, 157, 158, 159, 160, 162, 168, 169, 171, 173, 174, 176, 177, 180, 181, 182, 189, 190, 191, 192, 194, 195, 197, 199, 200, 201, 202, 204, 208, 209, 210, 212, 213, 214, 217, 218, 223, 224, 225, 226, 228, 229, 230, 232, 233, 234, 236, 238, 239}

def g32p_centralizerBound089_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (20, 3), (70, 6)}

theorem g32p_centralizerBound089_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) := by
  decide +kernel

theorem g32p_centralizerBound089_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 89) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound089_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound089_point_block00 t
  · exact g32p_centralizerBound089_point_block01 t
  · exact g32p_centralizerBound089_point_block02 t
  · exact g32p_centralizerBound089_point_block03 t
  · exact g32p_centralizerBound089_point_block04 t
  · exact g32p_centralizerBound089_point_block05 t
  · exact g32p_centralizerBound089_point_block06 t
  · exact g32p_centralizerBound089_point_block07 t
  · exact g32p_centralizerBound089_point_block08 t
  · exact g32p_centralizerBound089_point_block09 t
  · exact g32p_centralizerBound089_point_block10 t
  · exact g32p_centralizerBound089_point_block11 t
  · exact g32p_centralizerBound089_point_block12 t
  · exact g32p_centralizerBound089_point_block13 t
  · exact g32p_centralizerBound089_point_block14 t

theorem g32p_centralizerBound089_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 89) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 89)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound089_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound089_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 89) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 89)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound089_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound089_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 89) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 89)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound089_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound089_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 89) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 89)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound089_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound089_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 89) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 89)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound089_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound089_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 89) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 89) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound089_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 89) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 89)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound089_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound089_stabilizer_block00 t r
  · exact g32p_centralizerBound089_stabilizer_block01 t r
  · exact g32p_centralizerBound089_stabilizer_block02 t r
  · exact g32p_centralizerBound089_stabilizer_block03 t r
  · exact g32p_centralizerBound089_stabilizer_block04 t r

theorem g32p_centralizerBound089_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 89}) ≤ g32p_literalCentralizer 89 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 89 g32p_centralizerBound089_points
    g32p_centralizerBound089_stabilizers ?_ g32p_centralizerBound089_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound089_point_mem i (g32p_centralizer_point_moments 89 x i hi.symm)

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

def g32p_centralizerBound090_points : Finset (Fin 240) :=
  {0, 1, 3, 4, 6, 8, 9, 13, 15, 17, 18, 22, 23, 27, 28, 29, 30, 32, 36, 39, 40, 44, 45, 49, 50, 51, 52, 54, 58, 60, 62, 67, 69, 70, 71, 72, 73, 81, 85, 86, 90, 91, 92, 93, 95, 99, 101, 103, 108, 110, 111, 112, 113, 114, 122, 126, 127, 128, 129, 134, 135, 136, 140, 146, 150, 152, 157, 159, 160, 161, 162, 163, 171, 175, 176, 177, 182, 183, 184, 188, 193, 197, 198, 202, 203, 205, 210, 213, 214, 219, 222, 230, 231, 234, 236, 237}

def g32p_centralizerBound090_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (43, 1), (55, 1)}

theorem g32p_centralizerBound090_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) := by
  decide +kernel

theorem g32p_centralizerBound090_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 90) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound090_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound090_point_block00 t
  · exact g32p_centralizerBound090_point_block01 t
  · exact g32p_centralizerBound090_point_block02 t
  · exact g32p_centralizerBound090_point_block03 t
  · exact g32p_centralizerBound090_point_block04 t
  · exact g32p_centralizerBound090_point_block05 t
  · exact g32p_centralizerBound090_point_block06 t
  · exact g32p_centralizerBound090_point_block07 t
  · exact g32p_centralizerBound090_point_block08 t
  · exact g32p_centralizerBound090_point_block09 t
  · exact g32p_centralizerBound090_point_block10 t
  · exact g32p_centralizerBound090_point_block11 t
  · exact g32p_centralizerBound090_point_block12 t
  · exact g32p_centralizerBound090_point_block13 t
  · exact g32p_centralizerBound090_point_block14 t

theorem g32p_centralizerBound090_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 90) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 90)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound090_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound090_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 90) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 90)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound090_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound090_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 90) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 90)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound090_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound090_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 90) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 90)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound090_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound090_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 90) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 90)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound090_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound090_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 90) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 90) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound090_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 90) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 90)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound090_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound090_stabilizer_block00 t r
  · exact g32p_centralizerBound090_stabilizer_block01 t r
  · exact g32p_centralizerBound090_stabilizer_block02 t r
  · exact g32p_centralizerBound090_stabilizer_block03 t r
  · exact g32p_centralizerBound090_stabilizer_block04 t r

theorem g32p_centralizerBound090_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 90}) ≤ g32p_literalCentralizer 90 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 90 g32p_centralizerBound090_points
    g32p_centralizerBound090_stabilizers ?_ g32p_centralizerBound090_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound090_point_mem i (g32p_centralizer_point_moments 90 x i hi.symm)

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

def g32p_centralizerBound091_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 99, 133, 138, 142, 149, 181, 186, 189, 196, 206, 218, 223, 227}

def g32p_centralizerBound091_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (7, 8), (10, 5), (12, 7), (14, 5), (15, 7), (19, 0), (23, 4), (27, 4), (32, 4), (33, 6), (36, 1), (37, 2), (39, 2), (41, 6), (48, 6), (50, 2), (52, 6), (60, 5), (62, 2), (63, 7), (66, 0), (71, 1)}

theorem g32p_centralizerBound091_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) := by
  decide +kernel

theorem g32p_centralizerBound091_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 91) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound091_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound091_point_block00 t
  · exact g32p_centralizerBound091_point_block01 t
  · exact g32p_centralizerBound091_point_block02 t
  · exact g32p_centralizerBound091_point_block03 t
  · exact g32p_centralizerBound091_point_block04 t
  · exact g32p_centralizerBound091_point_block05 t
  · exact g32p_centralizerBound091_point_block06 t
  · exact g32p_centralizerBound091_point_block07 t
  · exact g32p_centralizerBound091_point_block08 t
  · exact g32p_centralizerBound091_point_block09 t
  · exact g32p_centralizerBound091_point_block10 t
  · exact g32p_centralizerBound091_point_block11 t
  · exact g32p_centralizerBound091_point_block12 t
  · exact g32p_centralizerBound091_point_block13 t
  · exact g32p_centralizerBound091_point_block14 t

theorem g32p_centralizerBound091_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 91) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 91)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound091_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound091_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 91) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 91)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound091_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound091_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 91) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 91)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound091_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound091_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 91) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 91)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound091_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound091_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 91) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 91)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound091_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound091_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 91) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 91) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound091_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 91) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 91)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound091_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound091_stabilizer_block00 t r
  · exact g32p_centralizerBound091_stabilizer_block01 t r
  · exact g32p_centralizerBound091_stabilizer_block02 t r
  · exact g32p_centralizerBound091_stabilizer_block03 t r
  · exact g32p_centralizerBound091_stabilizer_block04 t r

theorem g32p_centralizerBound091_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 91}) ≤ g32p_literalCentralizer 91 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 91 g32p_centralizerBound091_points
    g32p_centralizerBound091_stabilizers ?_ g32p_centralizerBound091_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound091_point_mem i (g32p_centralizer_point_moments 91 x i hi.symm)

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

def g32p_centralizerBound092_points : Finset (Fin 240) :=
  {3, 6, 15, 24, 36, 46, 58, 87, 99, 131, 179, 216}

def g32p_centralizerBound092_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 5), (4, 1), (5, 2), (6, 0), (7, 0), (8, 8), (9, 6), (10, 5), (11, 1), (13, 5), (15, 5), (17, 4), (19, 8), (20, 3), (21, 1), (22, 8), (23, 2), (25, 3), (26, 2), (27, 0), (29, 1), (30, 2), (31, 0), (32, 7), (33, 0), (34, 8), (35, 2), (37, 6), (38, 6), (39, 5), (40, 4), (41, 1), (42, 7), (43, 5), (44, 3), (47, 6), (48, 5), (49, 1), (51, 5), (53, 1), (56, 8), (57, 3), (58, 0), (59, 1), (60, 5), (63, 6), (64, 0), (65, 8), (66, 2), (68, 3), (69, 2), (70, 6), (71, 6)}

theorem g32p_centralizerBound092_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) := by
  decide +kernel

theorem g32p_centralizerBound092_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 92) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound092_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound092_point_block00 t
  · exact g32p_centralizerBound092_point_block01 t
  · exact g32p_centralizerBound092_point_block02 t
  · exact g32p_centralizerBound092_point_block03 t
  · exact g32p_centralizerBound092_point_block04 t
  · exact g32p_centralizerBound092_point_block05 t
  · exact g32p_centralizerBound092_point_block06 t
  · exact g32p_centralizerBound092_point_block07 t
  · exact g32p_centralizerBound092_point_block08 t
  · exact g32p_centralizerBound092_point_block09 t
  · exact g32p_centralizerBound092_point_block10 t
  · exact g32p_centralizerBound092_point_block11 t
  · exact g32p_centralizerBound092_point_block12 t
  · exact g32p_centralizerBound092_point_block13 t
  · exact g32p_centralizerBound092_point_block14 t

theorem g32p_centralizerBound092_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 92) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 92)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound092_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound092_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 92) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 92)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound092_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound092_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 92) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 92)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound092_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound092_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 92) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 92)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound092_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound092_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 92) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 92)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound092_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound092_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 92) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 92) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound092_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 92) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 92)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound092_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound092_stabilizer_block00 t r
  · exact g32p_centralizerBound092_stabilizer_block01 t r
  · exact g32p_centralizerBound092_stabilizer_block02 t r
  · exact g32p_centralizerBound092_stabilizer_block03 t r
  · exact g32p_centralizerBound092_stabilizer_block04 t r

theorem g32p_centralizerBound092_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 92}) ≤ g32p_literalCentralizer 92 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 92 g32p_centralizerBound092_points
    g32p_centralizerBound092_stabilizers ?_ g32p_centralizerBound092_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound092_point_mem i (g32p_centralizer_point_moments 92 x i hi.symm)

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

def g32p_centralizerBound093_points : Finset (Fin 240) :=
  {3, 6, 9, 10, 11, 13, 15, 18, 19, 20, 22, 24, 26, 27, 28, 30, 31, 32, 35, 36, 40, 41, 42, 44, 46, 48, 49, 50, 52, 53, 54, 57, 58, 61, 62, 63, 64, 65, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 79, 80, 82, 83, 85, 87, 89, 90, 91, 93, 94, 95, 98, 99, 102, 103, 104, 105, 106, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 120, 121, 123, 124, 126, 127, 128, 129, 130, 131, 132, 134, 137, 138, 139, 140, 141, 143, 145, 148, 149, 151, 152, 153, 154, 155, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 169, 170, 172, 173, 175, 176, 177, 178, 179, 180, 182, 185, 186, 187, 188, 190, 192, 195, 196, 197, 200, 201, 202, 203, 206, 207, 208, 211, 212, 213, 214, 215, 216, 217, 220, 221, 222, 224, 226, 227, 228, 229, 230, 231, 232, 235, 237, 238, 239}

def g32p_centralizerBound093_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 2), (0, 5), (6, 1), (6, 4), (6, 7), (10, 0), (10, 2), (10, 5), (24, 0), (24, 2), (24, 5), (43, 1), (43, 4), (43, 7), (53, 3), (53, 6), (53, 8), (55, 1), (55, 4), (55, 7), (60, 0), (60, 2), (60, 5)}

theorem g32p_centralizerBound093_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) := by
  decide +kernel

theorem g32p_centralizerBound093_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 93) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound093_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound093_point_block00 t
  · exact g32p_centralizerBound093_point_block01 t
  · exact g32p_centralizerBound093_point_block02 t
  · exact g32p_centralizerBound093_point_block03 t
  · exact g32p_centralizerBound093_point_block04 t
  · exact g32p_centralizerBound093_point_block05 t
  · exact g32p_centralizerBound093_point_block06 t
  · exact g32p_centralizerBound093_point_block07 t
  · exact g32p_centralizerBound093_point_block08 t
  · exact g32p_centralizerBound093_point_block09 t
  · exact g32p_centralizerBound093_point_block10 t
  · exact g32p_centralizerBound093_point_block11 t
  · exact g32p_centralizerBound093_point_block12 t
  · exact g32p_centralizerBound093_point_block13 t
  · exact g32p_centralizerBound093_point_block14 t

theorem g32p_centralizerBound093_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 93) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 93)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound093_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound093_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 93) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 93)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound093_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound093_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 93) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 93)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound093_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound093_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 93) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 93)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound093_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound093_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 93) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 93)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound093_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound093_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 93) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 93) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound093_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 93) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 93)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound093_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound093_stabilizer_block00 t r
  · exact g32p_centralizerBound093_stabilizer_block01 t r
  · exact g32p_centralizerBound093_stabilizer_block02 t r
  · exact g32p_centralizerBound093_stabilizer_block03 t r
  · exact g32p_centralizerBound093_stabilizer_block04 t r

theorem g32p_centralizerBound093_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 93}) ≤ g32p_literalCentralizer 93 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 93 g32p_centralizerBound093_points
    g32p_centralizerBound093_stabilizers ?_ g32p_centralizerBound093_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound093_point_mem i (g32p_centralizer_point_moments 93 x i hi.symm)

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

def g32p_centralizerBound094_points : Finset (Fin 240) :=
  {3, 6, 15, 28, 36, 50, 58, 91, 99, 127, 132, 134, 136, 143, 146, 180, 182, 184, 190, 193, 198, 217, 219, 224}

def g32p_centralizerBound094_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (6, 0), (7, 0), (11, 7), (17, 1), (20, 8), (27, 0), (31, 0), (44, 8), (49, 7), (57, 8), (64, 0)}

theorem g32p_centralizerBound094_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) := by
  decide +kernel

theorem g32p_centralizerBound094_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 94) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound094_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound094_point_block00 t
  · exact g32p_centralizerBound094_point_block01 t
  · exact g32p_centralizerBound094_point_block02 t
  · exact g32p_centralizerBound094_point_block03 t
  · exact g32p_centralizerBound094_point_block04 t
  · exact g32p_centralizerBound094_point_block05 t
  · exact g32p_centralizerBound094_point_block06 t
  · exact g32p_centralizerBound094_point_block07 t
  · exact g32p_centralizerBound094_point_block08 t
  · exact g32p_centralizerBound094_point_block09 t
  · exact g32p_centralizerBound094_point_block10 t
  · exact g32p_centralizerBound094_point_block11 t
  · exact g32p_centralizerBound094_point_block12 t
  · exact g32p_centralizerBound094_point_block13 t
  · exact g32p_centralizerBound094_point_block14 t

theorem g32p_centralizerBound094_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 94) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 94)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound094_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound094_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 94) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 94)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound094_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound094_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 94) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 94)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound094_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound094_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 94) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 94)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound094_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound094_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 94) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 94)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound094_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound094_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 94) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 94) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound094_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 94) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 94)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound094_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound094_stabilizer_block00 t r
  · exact g32p_centralizerBound094_stabilizer_block01 t r
  · exact g32p_centralizerBound094_stabilizer_block02 t r
  · exact g32p_centralizerBound094_stabilizer_block03 t r
  · exact g32p_centralizerBound094_stabilizer_block04 t r

theorem g32p_centralizerBound094_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 94}) ≤ g32p_literalCentralizer 94 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 94 g32p_centralizerBound094_points
    g32p_centralizerBound094_stabilizers ?_ g32p_centralizerBound094_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound094_point_mem i (g32p_centralizer_point_moments 94 x i hi.symm)

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

def g32p_centralizerBound095_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 99}

def g32p_centralizerBound095_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  Finset.univ

theorem g32p_centralizerBound095_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) := by
  decide +kernel

theorem g32p_centralizerBound095_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 95) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound095_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound095_point_block00 t
  · exact g32p_centralizerBound095_point_block01 t
  · exact g32p_centralizerBound095_point_block02 t
  · exact g32p_centralizerBound095_point_block03 t
  · exact g32p_centralizerBound095_point_block04 t
  · exact g32p_centralizerBound095_point_block05 t
  · exact g32p_centralizerBound095_point_block06 t
  · exact g32p_centralizerBound095_point_block07 t
  · exact g32p_centralizerBound095_point_block08 t
  · exact g32p_centralizerBound095_point_block09 t
  · exact g32p_centralizerBound095_point_block10 t
  · exact g32p_centralizerBound095_point_block11 t
  · exact g32p_centralizerBound095_point_block12 t
  · exact g32p_centralizerBound095_point_block13 t
  · exact g32p_centralizerBound095_point_block14 t

theorem g32p_centralizerBound095_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 95) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 95)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound095_stabilizers) := by
  intro t r
  dsimp only
  intro _
  exact Finset.mem_univ _

theorem g32p_centralizerBound095_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 95) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 95)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound095_stabilizers) := by
  intro t r
  dsimp only
  intro _
  exact Finset.mem_univ _

theorem g32p_centralizerBound095_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 95) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 95)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound095_stabilizers) := by
  intro t r
  dsimp only
  intro _
  exact Finset.mem_univ _

theorem g32p_centralizerBound095_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 95) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 95)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound095_stabilizers) := by
  intro t r
  dsimp only
  intro _
  exact Finset.mem_univ _

theorem g32p_centralizerBound095_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 95) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 95)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound095_stabilizers) := by
  intro t r
  dsimp only
  intro _
  exact Finset.mem_univ _

theorem g32p_centralizerBound095_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 95) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 95) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound095_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 95) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 95)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound095_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound095_stabilizer_block00 t r
  · exact g32p_centralizerBound095_stabilizer_block01 t r
  · exact g32p_centralizerBound095_stabilizer_block02 t r
  · exact g32p_centralizerBound095_stabilizer_block03 t r
  · exact g32p_centralizerBound095_stabilizer_block04 t r

theorem g32p_centralizerBound095_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 95}) ≤ g32p_literalCentralizer 95 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 95 g32p_centralizerBound095_points
    g32p_centralizerBound095_stabilizers ?_ g32p_centralizerBound095_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound095_point_mem i (g32p_centralizer_point_moments 95 x i hi.symm)

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

def g32p_centralizerBound098_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 14, 15, 16, 20, 21, 24, 25, 26, 27, 28, 29, 30, 31, 36, 37, 38, 42, 43, 46, 47, 48, 49, 50, 51, 52, 53, 58, 59, 60, 61, 62, 63, 66, 69, 70, 71, 73, 74, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 87, 88, 89, 90, 91, 92, 93, 94, 99, 100, 101, 102, 103, 104, 107, 110, 111, 112, 114, 115, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 131, 132, 133, 134, 135, 137, 138, 140, 142, 143, 145, 149, 150, 151, 152, 153, 156, 159, 160, 161, 163, 164, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 179, 180, 181, 182, 183, 185, 186, 188, 189, 190, 192, 196, 203, 204, 205, 206, 207, 209, 210, 211, 213, 214, 216, 217, 218, 220, 222, 223, 224, 226, 227, 231, 233, 234, 235, 236, 237}

def g32p_centralizerBound098_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (8, 3), (8, 4), (8, 5), (10, 3), (10, 4), (10, 5), (16, 1), (16, 2), (16, 8), (18, 1), (18, 2), (18, 8), (49, 3), (49, 4), (49, 5), (60, 3), (60, 4), (60, 5), (68, 0), (68, 6), (68, 7)}

theorem g32p_centralizerBound098_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) := by
  decide +kernel

theorem g32p_centralizerBound098_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 98) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound098_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound098_point_block00 t
  · exact g32p_centralizerBound098_point_block01 t
  · exact g32p_centralizerBound098_point_block02 t
  · exact g32p_centralizerBound098_point_block03 t
  · exact g32p_centralizerBound098_point_block04 t
  · exact g32p_centralizerBound098_point_block05 t
  · exact g32p_centralizerBound098_point_block06 t
  · exact g32p_centralizerBound098_point_block07 t
  · exact g32p_centralizerBound098_point_block08 t
  · exact g32p_centralizerBound098_point_block09 t
  · exact g32p_centralizerBound098_point_block10 t
  · exact g32p_centralizerBound098_point_block11 t
  · exact g32p_centralizerBound098_point_block12 t
  · exact g32p_centralizerBound098_point_block13 t
  · exact g32p_centralizerBound098_point_block14 t

theorem g32p_centralizerBound098_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 98) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 98)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound098_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound098_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 98) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 98)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound098_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound098_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 98) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 98)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound098_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound098_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 98) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 98)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound098_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound098_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 98) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 98)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound098_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound098_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 98) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 98) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound098_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 98) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 98)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound098_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound098_stabilizer_block00 t r
  · exact g32p_centralizerBound098_stabilizer_block01 t r
  · exact g32p_centralizerBound098_stabilizer_block02 t r
  · exact g32p_centralizerBound098_stabilizer_block03 t r
  · exact g32p_centralizerBound098_stabilizer_block04 t r

theorem g32p_centralizerBound098_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 98}) ≤ g32p_literalCentralizer 98 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 98 g32p_centralizerBound098_points
    g32p_centralizerBound098_stabilizers ?_ g32p_centralizerBound098_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound098_point_mem i (g32p_centralizer_point_moments 98 x i hi.symm)

end HodgeLean.Foundations.Program

end
end
