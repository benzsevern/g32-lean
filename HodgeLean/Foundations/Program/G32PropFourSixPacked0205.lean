import HodgeLean.Foundations.Program.G32PropFourSixPacked0201
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound065_points : Finset (Fin 240) :=
  {3, 6, 9, 10, 11, 12, 13, 15, 18, 19, 20, 21, 22, 24, 26, 27, 28, 30, 31, 32, 33, 34, 35, 36, 37, 40, 41, 42, 43, 44, 46, 48, 49, 50, 52, 53, 54, 55, 56, 57, 58, 59, 61, 62, 63, 64, 65, 67, 68, 69, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 83, 84, 85, 87, 89, 90, 91, 93, 94, 95, 96, 97, 98, 99, 100, 102, 103, 104, 105, 106, 108, 109, 110, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 124, 125, 126, 127, 128, 130, 131, 132, 133, 134, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 151, 152, 153, 154, 155, 157, 158, 159, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 173, 174, 175, 176, 178, 179, 180, 181, 182, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 202, 203, 204, 206, 209, 210, 212, 213, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 230, 231, 233, 234, 236, 237}

def g32p_centralizerBound065_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (18, 2), (22, 7), (24, 2), (30, 4), (36, 5), (53, 8), (63, 3), (68, 7)}

theorem g32p_centralizerBound065_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) := by
  decide +kernel

theorem g32p_centralizerBound065_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 65) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound065_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound065_point_block00 t
  · exact g32p_centralizerBound065_point_block01 t
  · exact g32p_centralizerBound065_point_block02 t
  · exact g32p_centralizerBound065_point_block03 t
  · exact g32p_centralizerBound065_point_block04 t
  · exact g32p_centralizerBound065_point_block05 t
  · exact g32p_centralizerBound065_point_block06 t
  · exact g32p_centralizerBound065_point_block07 t
  · exact g32p_centralizerBound065_point_block08 t
  · exact g32p_centralizerBound065_point_block09 t
  · exact g32p_centralizerBound065_point_block10 t
  · exact g32p_centralizerBound065_point_block11 t
  · exact g32p_centralizerBound065_point_block12 t
  · exact g32p_centralizerBound065_point_block13 t
  · exact g32p_centralizerBound065_point_block14 t

theorem g32p_centralizerBound065_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 65) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 65)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound065_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound065_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 65) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 65)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound065_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound065_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 65) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 65)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound065_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound065_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 65) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 65)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound065_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound065_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 65) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 65)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound065_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound065_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 65) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 65) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound065_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 65) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 65)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound065_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound065_stabilizer_block00 t r
  · exact g32p_centralizerBound065_stabilizer_block01 t r
  · exact g32p_centralizerBound065_stabilizer_block02 t r
  · exact g32p_centralizerBound065_stabilizer_block03 t r
  · exact g32p_centralizerBound065_stabilizer_block04 t r

theorem g32p_centralizerBound065_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 65}) ≤ g32p_literalCentralizer 65 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 65 g32p_centralizerBound065_points
    g32p_centralizerBound065_stabilizers ?_ g32p_centralizerBound065_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound065_point_mem i (g32p_centralizer_point_moments 65 x i hi.symm)

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

def g32p_centralizerBound066_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 9, 11, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 29, 31, 33, 34, 35, 36, 38, 40, 42, 43, 46, 47, 49, 50, 51, 53, 55, 56, 57, 58, 62, 64, 66, 67, 70, 75, 76, 79, 83, 84, 87, 88, 90, 91, 92, 94, 96, 97, 98, 99, 103, 105, 107, 108, 111, 116, 117, 120, 124, 125, 127, 129, 130, 131, 134, 135, 139, 141, 144, 145, 147, 148, 152, 154, 156, 157, 160, 165, 166, 169, 173, 174, 177, 178, 179, 182, 183, 187, 191, 192, 194, 195, 199, 205, 214, 215, 216, 221, 225, 226}

def g32p_centralizerBound066_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound066_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) := by
  decide +kernel

theorem g32p_centralizerBound066_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 66) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound066_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound066_point_block00 t
  · exact g32p_centralizerBound066_point_block01 t
  · exact g32p_centralizerBound066_point_block02 t
  · exact g32p_centralizerBound066_point_block03 t
  · exact g32p_centralizerBound066_point_block04 t
  · exact g32p_centralizerBound066_point_block05 t
  · exact g32p_centralizerBound066_point_block06 t
  · exact g32p_centralizerBound066_point_block07 t
  · exact g32p_centralizerBound066_point_block08 t
  · exact g32p_centralizerBound066_point_block09 t
  · exact g32p_centralizerBound066_point_block10 t
  · exact g32p_centralizerBound066_point_block11 t
  · exact g32p_centralizerBound066_point_block12 t
  · exact g32p_centralizerBound066_point_block13 t
  · exact g32p_centralizerBound066_point_block14 t

theorem g32p_centralizerBound066_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 66) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 66)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound066_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound066_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 66) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 66)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound066_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound066_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 66) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 66)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound066_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound066_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 66) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 66)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound066_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound066_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 66) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 66)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound066_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound066_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 66) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 66) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound066_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 66) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 66)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound066_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound066_stabilizer_block00 t r
  · exact g32p_centralizerBound066_stabilizer_block01 t r
  · exact g32p_centralizerBound066_stabilizer_block02 t r
  · exact g32p_centralizerBound066_stabilizer_block03 t r
  · exact g32p_centralizerBound066_stabilizer_block04 t r

theorem g32p_centralizerBound066_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 66}) ≤ g32p_literalCentralizer 66 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 66 g32p_centralizerBound066_points
    g32p_centralizerBound066_stabilizers ?_ g32p_centralizerBound066_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound066_point_mem i (g32p_centralizer_point_moments 66 x i hi.symm)

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

def g32p_centralizerBound067_points : Finset (Fin 240) :=
  {3, 6, 10, 11, 12, 13, 15, 19, 20, 21, 22, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 41, 42, 43, 44, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 65, 68, 70, 71, 73, 74, 75, 76, 77, 78, 79, 81, 83, 84, 85, 90, 92, 93, 94, 95, 96, 97, 98, 99, 100, 103, 106, 109, 111, 112, 114, 115, 116, 117, 118, 119, 120, 122, 124, 125, 126, 129, 132, 133, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 152, 155, 158, 160, 161, 163, 164, 165, 166, 167, 168, 169, 171, 173, 174, 175, 177, 180, 181, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 198, 199, 200, 201, 203, 204, 205, 206, 208, 209, 210, 212, 214, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 231, 232, 233, 234, 236, 237, 238, 239}

def g32p_centralizerBound067_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (12, 0), (12, 6), (12, 7), (20, 3), (20, 4), (20, 5), (24, 1), (24, 2), (24, 8), (26, 1), (26, 2), (26, 8), (53, 1), (53, 2), (53, 8), (70, 0), (70, 6), (70, 7)}

theorem g32p_centralizerBound067_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) := by
  decide +kernel

theorem g32p_centralizerBound067_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 67) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound067_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound067_point_block00 t
  · exact g32p_centralizerBound067_point_block01 t
  · exact g32p_centralizerBound067_point_block02 t
  · exact g32p_centralizerBound067_point_block03 t
  · exact g32p_centralizerBound067_point_block04 t
  · exact g32p_centralizerBound067_point_block05 t
  · exact g32p_centralizerBound067_point_block06 t
  · exact g32p_centralizerBound067_point_block07 t
  · exact g32p_centralizerBound067_point_block08 t
  · exact g32p_centralizerBound067_point_block09 t
  · exact g32p_centralizerBound067_point_block10 t
  · exact g32p_centralizerBound067_point_block11 t
  · exact g32p_centralizerBound067_point_block12 t
  · exact g32p_centralizerBound067_point_block13 t
  · exact g32p_centralizerBound067_point_block14 t

theorem g32p_centralizerBound067_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 67) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 67)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound067_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound067_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 67) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 67)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound067_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound067_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 67) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 67)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound067_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound067_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 67) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 67)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound067_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound067_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 67) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 67)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound067_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound067_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 67) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 67) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound067_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 67) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 67)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound067_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound067_stabilizer_block00 t r
  · exact g32p_centralizerBound067_stabilizer_block01 t r
  · exact g32p_centralizerBound067_stabilizer_block02 t r
  · exact g32p_centralizerBound067_stabilizer_block03 t r
  · exact g32p_centralizerBound067_stabilizer_block04 t r

theorem g32p_centralizerBound067_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 67}) ≤ g32p_literalCentralizer 67 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 67 g32p_centralizerBound067_points
    g32p_centralizerBound067_stabilizers ?_ g32p_centralizerBound067_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound067_point_mem i (g32p_centralizer_point_moments 67 x i hi.symm)

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

def g32p_centralizerBound068_points : Finset (Fin 240) :=
  {3, 6, 10, 15, 19, 24, 27, 36, 41, 46, 49, 58, 62, 63, 64, 68, 75, 80, 85, 87, 90, 99, 103, 104, 105, 109, 116, 121, 126, 130, 131, 138, 139, 140, 149, 152, 153, 154, 158, 165, 170, 175, 178, 179, 186, 187, 188, 196, 206, 215, 216, 221, 222, 227}

def g32p_centralizerBound068_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound068_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) := by
  decide +kernel

theorem g32p_centralizerBound068_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 68) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound068_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound068_point_block00 t
  · exact g32p_centralizerBound068_point_block01 t
  · exact g32p_centralizerBound068_point_block02 t
  · exact g32p_centralizerBound068_point_block03 t
  · exact g32p_centralizerBound068_point_block04 t
  · exact g32p_centralizerBound068_point_block05 t
  · exact g32p_centralizerBound068_point_block06 t
  · exact g32p_centralizerBound068_point_block07 t
  · exact g32p_centralizerBound068_point_block08 t
  · exact g32p_centralizerBound068_point_block09 t
  · exact g32p_centralizerBound068_point_block10 t
  · exact g32p_centralizerBound068_point_block11 t
  · exact g32p_centralizerBound068_point_block12 t
  · exact g32p_centralizerBound068_point_block13 t
  · exact g32p_centralizerBound068_point_block14 t

theorem g32p_centralizerBound068_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 68) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 68)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound068_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound068_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 68) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 68)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound068_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound068_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 68) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 68)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound068_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound068_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 68) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 68)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound068_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound068_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 68) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 68)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound068_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound068_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 68) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 68) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound068_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 68) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 68)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound068_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound068_stabilizer_block00 t r
  · exact g32p_centralizerBound068_stabilizer_block01 t r
  · exact g32p_centralizerBound068_stabilizer_block02 t r
  · exact g32p_centralizerBound068_stabilizer_block03 t r
  · exact g32p_centralizerBound068_stabilizer_block04 t r

theorem g32p_centralizerBound068_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 68}) ≤ g32p_literalCentralizer 68 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 68 g32p_centralizerBound068_points
    g32p_centralizerBound068_stabilizers ?_ g32p_centralizerBound068_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound068_point_mem i (g32p_centralizer_point_moments 68 x i hi.symm)

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

def g32p_centralizerBound069_points : Finset (Fin 240) :=
  {3, 6, 9, 10, 12, 15, 18, 19, 21, 24, 26, 27, 35, 36, 40, 41, 43, 46, 48, 49, 57, 58, 61, 62, 65, 67, 68, 75, 84, 87, 89, 90, 98, 99, 102, 103, 106, 108, 109, 116, 125, 131, 133, 136, 139, 141, 142, 146, 148, 151, 152, 155, 157, 158, 165, 174, 179, 181, 184, 187, 189, 193, 195, 198, 200, 212, 216, 218, 219, 221, 223, 228}

def g32p_centralizerBound069_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (20, 8), (49, 7), (64, 0)}

theorem g32p_centralizerBound069_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) := by
  decide +kernel

theorem g32p_centralizerBound069_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 69) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound069_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound069_point_block00 t
  · exact g32p_centralizerBound069_point_block01 t
  · exact g32p_centralizerBound069_point_block02 t
  · exact g32p_centralizerBound069_point_block03 t
  · exact g32p_centralizerBound069_point_block04 t
  · exact g32p_centralizerBound069_point_block05 t
  · exact g32p_centralizerBound069_point_block06 t
  · exact g32p_centralizerBound069_point_block07 t
  · exact g32p_centralizerBound069_point_block08 t
  · exact g32p_centralizerBound069_point_block09 t
  · exact g32p_centralizerBound069_point_block10 t
  · exact g32p_centralizerBound069_point_block11 t
  · exact g32p_centralizerBound069_point_block12 t
  · exact g32p_centralizerBound069_point_block13 t
  · exact g32p_centralizerBound069_point_block14 t

theorem g32p_centralizerBound069_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 69) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 69)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound069_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound069_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 69) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 69)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound069_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound069_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 69) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 69)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound069_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound069_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 69) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 69)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound069_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound069_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 69) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 69)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound069_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound069_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 69) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 69) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound069_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 69) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 69)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound069_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound069_stabilizer_block00 t r
  · exact g32p_centralizerBound069_stabilizer_block01 t r
  · exact g32p_centralizerBound069_stabilizer_block02 t r
  · exact g32p_centralizerBound069_stabilizer_block03 t r
  · exact g32p_centralizerBound069_stabilizer_block04 t r

theorem g32p_centralizerBound069_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 69}) ≤ g32p_literalCentralizer 69 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 69 g32p_centralizerBound069_points
    g32p_centralizerBound069_stabilizers ?_ g32p_centralizerBound069_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound069_point_mem i (g32p_centralizer_point_moments 69 x i hi.symm)

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

def g32p_centralizerBound070_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 63, 80, 99, 104, 121, 133, 142, 153, 170, 181, 189, 218, 223}

def g32p_centralizerBound070_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (14, 5), (32, 4)}

theorem g32p_centralizerBound070_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) := by
  decide +kernel

theorem g32p_centralizerBound070_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 70) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound070_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound070_point_block00 t
  · exact g32p_centralizerBound070_point_block01 t
  · exact g32p_centralizerBound070_point_block02 t
  · exact g32p_centralizerBound070_point_block03 t
  · exact g32p_centralizerBound070_point_block04 t
  · exact g32p_centralizerBound070_point_block05 t
  · exact g32p_centralizerBound070_point_block06 t
  · exact g32p_centralizerBound070_point_block07 t
  · exact g32p_centralizerBound070_point_block08 t
  · exact g32p_centralizerBound070_point_block09 t
  · exact g32p_centralizerBound070_point_block10 t
  · exact g32p_centralizerBound070_point_block11 t
  · exact g32p_centralizerBound070_point_block12 t
  · exact g32p_centralizerBound070_point_block13 t
  · exact g32p_centralizerBound070_point_block14 t

theorem g32p_centralizerBound070_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 70) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 70)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound070_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound070_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 70) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 70)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound070_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound070_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 70) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 70)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound070_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound070_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 70) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 70)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound070_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound070_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 70) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 70)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound070_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound070_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 70) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 70) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound070_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 70) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 70)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound070_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound070_stabilizer_block00 t r
  · exact g32p_centralizerBound070_stabilizer_block01 t r
  · exact g32p_centralizerBound070_stabilizer_block02 t r
  · exact g32p_centralizerBound070_stabilizer_block03 t r
  · exact g32p_centralizerBound070_stabilizer_block04 t r

theorem g32p_centralizerBound070_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 70}) ≤ g32p_literalCentralizer 70 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 70 g32p_centralizerBound070_points
    g32p_centralizerBound070_stabilizers ?_ g32p_centralizerBound070_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound070_point_mem i (g32p_centralizer_point_moments 70 x i hi.symm)

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

def g32p_centralizerBound071_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 9, 14, 15, 18, 25, 36, 40, 47, 58, 63, 67, 80, 88, 99, 104, 108, 121, 132, 136, 143, 146, 153, 157, 170, 180, 184, 190, 193, 198, 217, 219, 224}

def g32p_centralizerBound071_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (14, 5), (32, 4)}

theorem g32p_centralizerBound071_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) := by
  decide +kernel

theorem g32p_centralizerBound071_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 71) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound071_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound071_point_block00 t
  · exact g32p_centralizerBound071_point_block01 t
  · exact g32p_centralizerBound071_point_block02 t
  · exact g32p_centralizerBound071_point_block03 t
  · exact g32p_centralizerBound071_point_block04 t
  · exact g32p_centralizerBound071_point_block05 t
  · exact g32p_centralizerBound071_point_block06 t
  · exact g32p_centralizerBound071_point_block07 t
  · exact g32p_centralizerBound071_point_block08 t
  · exact g32p_centralizerBound071_point_block09 t
  · exact g32p_centralizerBound071_point_block10 t
  · exact g32p_centralizerBound071_point_block11 t
  · exact g32p_centralizerBound071_point_block12 t
  · exact g32p_centralizerBound071_point_block13 t
  · exact g32p_centralizerBound071_point_block14 t

theorem g32p_centralizerBound071_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 71) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 71)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound071_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound071_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 71) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 71)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound071_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound071_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 71) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 71)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound071_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound071_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 71) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 71)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound071_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound071_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 71) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 71)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound071_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound071_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 71) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 71) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound071_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 71) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 71)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound071_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound071_stabilizer_block00 t r
  · exact g32p_centralizerBound071_stabilizer_block01 t r
  · exact g32p_centralizerBound071_stabilizer_block02 t r
  · exact g32p_centralizerBound071_stabilizer_block03 t r
  · exact g32p_centralizerBound071_stabilizer_block04 t r

theorem g32p_centralizerBound071_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 71}) ≤ g32p_literalCentralizer 71 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 71 g32p_centralizerBound071_points
    g32p_centralizerBound071_stabilizers ?_ g32p_centralizerBound071_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound071_point_mem i (g32p_centralizer_point_moments 71 x i hi.symm)

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

def g32p_centralizerBound072_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 82, 99, 123, 172, 207, 211, 235}

def g32p_centralizerBound072_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (12, 0), (24, 2), (26, 2), (53, 8), (70, 0)}

theorem g32p_centralizerBound072_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) := by
  decide +kernel

theorem g32p_centralizerBound072_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 72) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound072_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound072_point_block00 t
  · exact g32p_centralizerBound072_point_block01 t
  · exact g32p_centralizerBound072_point_block02 t
  · exact g32p_centralizerBound072_point_block03 t
  · exact g32p_centralizerBound072_point_block04 t
  · exact g32p_centralizerBound072_point_block05 t
  · exact g32p_centralizerBound072_point_block06 t
  · exact g32p_centralizerBound072_point_block07 t
  · exact g32p_centralizerBound072_point_block08 t
  · exact g32p_centralizerBound072_point_block09 t
  · exact g32p_centralizerBound072_point_block10 t
  · exact g32p_centralizerBound072_point_block11 t
  · exact g32p_centralizerBound072_point_block12 t
  · exact g32p_centralizerBound072_point_block13 t
  · exact g32p_centralizerBound072_point_block14 t

theorem g32p_centralizerBound072_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 72) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 72)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound072_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound072_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 72) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 72)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound072_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound072_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 72) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 72)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound072_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound072_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 72) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 72)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound072_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound072_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 72) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 72)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound072_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound072_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 72) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 72) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound072_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 72) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 72)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound072_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound072_stabilizer_block00 t r
  · exact g32p_centralizerBound072_stabilizer_block01 t r
  · exact g32p_centralizerBound072_stabilizer_block02 t r
  · exact g32p_centralizerBound072_stabilizer_block03 t r
  · exact g32p_centralizerBound072_stabilizer_block04 t r

theorem g32p_centralizerBound072_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 72}) ≤ g32p_literalCentralizer 72 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 72 g32p_centralizerBound072_points
    g32p_centralizerBound072_stabilizers ?_ g32p_centralizerBound072_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound072_point_mem i (g32p_centralizer_point_moments 72 x i hi.symm)

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

def g32p_centralizerBound073_points : Finset (Fin 240) :=
  {3, 6, 10, 15, 19, 35, 36, 41, 57, 58, 65, 68, 98, 99, 106, 109, 138, 141, 148, 149, 155, 158, 186, 195, 196, 200, 206, 212, 227, 228}

def g32p_centralizerBound073_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound073_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) := by
  decide +kernel

theorem g32p_centralizerBound073_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 73) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound073_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound073_point_block00 t
  · exact g32p_centralizerBound073_point_block01 t
  · exact g32p_centralizerBound073_point_block02 t
  · exact g32p_centralizerBound073_point_block03 t
  · exact g32p_centralizerBound073_point_block04 t
  · exact g32p_centralizerBound073_point_block05 t
  · exact g32p_centralizerBound073_point_block06 t
  · exact g32p_centralizerBound073_point_block07 t
  · exact g32p_centralizerBound073_point_block08 t
  · exact g32p_centralizerBound073_point_block09 t
  · exact g32p_centralizerBound073_point_block10 t
  · exact g32p_centralizerBound073_point_block11 t
  · exact g32p_centralizerBound073_point_block12 t
  · exact g32p_centralizerBound073_point_block13 t
  · exact g32p_centralizerBound073_point_block14 t

theorem g32p_centralizerBound073_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 73) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 73)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound073_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound073_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 73) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 73)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound073_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound073_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 73) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 73)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound073_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound073_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 73) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 73)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound073_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound073_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 73) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 73)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound073_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound073_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 73) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 73) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound073_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 73) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 73)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound073_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound073_stabilizer_block00 t r
  · exact g32p_centralizerBound073_stabilizer_block01 t r
  · exact g32p_centralizerBound073_stabilizer_block02 t r
  · exact g32p_centralizerBound073_stabilizer_block03 t r
  · exact g32p_centralizerBound073_stabilizer_block04 t r

theorem g32p_centralizerBound073_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 73}) ≤ g32p_literalCentralizer 73 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 73 g32p_centralizerBound073_points
    g32p_centralizerBound073_stabilizers ?_ g32p_centralizerBound073_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound073_point_mem i (g32p_centralizer_point_moments 73 x i hi.symm)

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

def g32p_centralizerBound074_points : Finset (Fin 240) :=
  {3, 6, 15, 36, 58, 99}

def g32p_centralizerBound074_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (7, 0), (8, 8), (12, 7), (15, 3), (17, 5), (20, 4), (24, 1), (26, 2), (27, 0), (39, 3), (44, 4), (50, 7), (54, 2), (62, 3), (67, 1), (69, 2)}

theorem g32p_centralizerBound074_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) := by
  decide +kernel

theorem g32p_centralizerBound074_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 74) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound074_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound074_point_block00 t
  · exact g32p_centralizerBound074_point_block01 t
  · exact g32p_centralizerBound074_point_block02 t
  · exact g32p_centralizerBound074_point_block03 t
  · exact g32p_centralizerBound074_point_block04 t
  · exact g32p_centralizerBound074_point_block05 t
  · exact g32p_centralizerBound074_point_block06 t
  · exact g32p_centralizerBound074_point_block07 t
  · exact g32p_centralizerBound074_point_block08 t
  · exact g32p_centralizerBound074_point_block09 t
  · exact g32p_centralizerBound074_point_block10 t
  · exact g32p_centralizerBound074_point_block11 t
  · exact g32p_centralizerBound074_point_block12 t
  · exact g32p_centralizerBound074_point_block13 t
  · exact g32p_centralizerBound074_point_block14 t

theorem g32p_centralizerBound074_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 74) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 74)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound074_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound074_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 74) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 74)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound074_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound074_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 74) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 74)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound074_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound074_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 74) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 74)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound074_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound074_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 74) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 74)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound074_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound074_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 74) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 74) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound074_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 74) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 74)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound074_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound074_stabilizer_block00 t r
  · exact g32p_centralizerBound074_stabilizer_block01 t r
  · exact g32p_centralizerBound074_stabilizer_block02 t r
  · exact g32p_centralizerBound074_stabilizer_block03 t r
  · exact g32p_centralizerBound074_stabilizer_block04 t r

theorem g32p_centralizerBound074_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 74}) ≤ g32p_literalCentralizer 74 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 74 g32p_centralizerBound074_points
    g32p_centralizerBound074_stabilizers ?_ g32p_centralizerBound074_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound074_point_mem i (g32p_centralizer_point_moments 74 x i hi.symm)

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

def g32p_centralizerBound075_points : Finset (Fin 240) :=
  {3, 6, 10, 15, 19, 27, 33, 36, 41, 49, 55, 58, 62, 68, 75, 78, 85, 90, 96, 99, 103, 109, 116, 119, 126, 133, 138, 139, 140, 142, 144, 149, 152, 158, 165, 168, 175, 181, 186, 187, 188, 189, 191, 196, 204, 206, 209, 218, 221, 222, 223, 225, 227, 233}

def g32p_centralizerBound075_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (12, 7), (20, 4), (24, 1), (26, 2)}

theorem g32p_centralizerBound075_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) := by
  decide +kernel

theorem g32p_centralizerBound075_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 75) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound075_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound075_point_block00 t
  · exact g32p_centralizerBound075_point_block01 t
  · exact g32p_centralizerBound075_point_block02 t
  · exact g32p_centralizerBound075_point_block03 t
  · exact g32p_centralizerBound075_point_block04 t
  · exact g32p_centralizerBound075_point_block05 t
  · exact g32p_centralizerBound075_point_block06 t
  · exact g32p_centralizerBound075_point_block07 t
  · exact g32p_centralizerBound075_point_block08 t
  · exact g32p_centralizerBound075_point_block09 t
  · exact g32p_centralizerBound075_point_block10 t
  · exact g32p_centralizerBound075_point_block11 t
  · exact g32p_centralizerBound075_point_block12 t
  · exact g32p_centralizerBound075_point_block13 t
  · exact g32p_centralizerBound075_point_block14 t

theorem g32p_centralizerBound075_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 75) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 75)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound075_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound075_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 75) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 75)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound075_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound075_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 75) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 75)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound075_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound075_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 75) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 75)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound075_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound075_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 75) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 75)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound075_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound075_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 75) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 75) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound075_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 75) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 75)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound075_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound075_stabilizer_block00 t r
  · exact g32p_centralizerBound075_stabilizer_block01 t r
  · exact g32p_centralizerBound075_stabilizer_block02 t r
  · exact g32p_centralizerBound075_stabilizer_block03 t r
  · exact g32p_centralizerBound075_stabilizer_block04 t r

theorem g32p_centralizerBound075_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 75}) ≤ g32p_literalCentralizer 75 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 75 g32p_centralizerBound075_points
    g32p_centralizerBound075_stabilizers ?_ g32p_centralizerBound075_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound075_point_mem i (g32p_centralizer_point_moments 75 x i hi.symm)

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

def g32p_centralizerBound076_points : Finset (Fin 240) :=
  {3, 6, 10, 11, 12, 13, 15, 19, 20, 21, 22, 27, 29, 30, 31, 32, 33, 34, 35, 36, 37, 41, 42, 43, 44, 49, 51, 52, 53, 54, 55, 56, 57, 58, 59, 62, 65, 68, 70, 71, 73, 74, 75, 76, 77, 78, 79, 81, 83, 84, 85, 90, 92, 93, 94, 95, 96, 97, 98, 99, 100, 103, 106, 109, 111, 112, 114, 115, 116, 117, 118, 119, 120, 122, 124, 125, 126, 129, 132, 133, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 152, 155, 158, 160, 161, 163, 164, 165, 166, 167, 168, 169, 171, 173, 174, 175, 177, 180, 181, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 198, 199, 200, 201, 203, 204, 205, 206, 208, 209, 210, 212, 214, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 231, 232, 233, 234, 236, 237, 238, 239}

def g32p_centralizerBound076_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (1, 3), (1, 4), (1, 5), (12, 0), (12, 6), (12, 7), (20, 3), (20, 4), (20, 5), (24, 1), (24, 2), (24, 8), (26, 1), (26, 2), (26, 8), (53, 1), (53, 2), (53, 8), (70, 0), (70, 6), (70, 7)}

theorem g32p_centralizerBound076_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) := by
  decide +kernel

theorem g32p_centralizerBound076_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 76) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound076_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound076_point_block00 t
  · exact g32p_centralizerBound076_point_block01 t
  · exact g32p_centralizerBound076_point_block02 t
  · exact g32p_centralizerBound076_point_block03 t
  · exact g32p_centralizerBound076_point_block04 t
  · exact g32p_centralizerBound076_point_block05 t
  · exact g32p_centralizerBound076_point_block06 t
  · exact g32p_centralizerBound076_point_block07 t
  · exact g32p_centralizerBound076_point_block08 t
  · exact g32p_centralizerBound076_point_block09 t
  · exact g32p_centralizerBound076_point_block10 t
  · exact g32p_centralizerBound076_point_block11 t
  · exact g32p_centralizerBound076_point_block12 t
  · exact g32p_centralizerBound076_point_block13 t
  · exact g32p_centralizerBound076_point_block14 t

theorem g32p_centralizerBound076_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 76) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 76)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound076_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound076_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 76) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 76)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound076_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound076_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 76) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 76)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound076_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound076_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 76) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 76)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound076_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound076_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 76) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 76)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound076_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound076_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 76) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 76) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound076_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 76) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 76)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound076_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound076_stabilizer_block00 t r
  · exact g32p_centralizerBound076_stabilizer_block01 t r
  · exact g32p_centralizerBound076_stabilizer_block02 t r
  · exact g32p_centralizerBound076_stabilizer_block03 t r
  · exact g32p_centralizerBound076_stabilizer_block04 t r

theorem g32p_centralizerBound076_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 76}) ≤ g32p_literalCentralizer 76 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 76 g32p_centralizerBound076_points
    g32p_centralizerBound076_stabilizers ?_ g32p_centralizerBound076_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound076_point_mem i (g32p_centralizer_point_moments 76 x i hi.symm)

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

def g32p_centralizerBound077_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 9, 11, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 28, 29, 30, 31, 33, 34, 35, 36, 38, 40, 42, 43, 46, 47, 49, 50, 51, 52, 53, 55, 56, 57, 58, 60, 62, 64, 65, 66, 67, 70, 71, 72, 74, 75, 76, 79, 83, 84, 87, 88, 90, 91, 92, 93, 94, 96, 97, 98, 99, 101, 103, 105, 106, 107, 108, 111, 112, 113, 115, 116, 117, 120, 124, 125, 127, 129, 130, 131, 134, 135, 136, 137, 139, 141, 144, 145, 146, 147, 148, 150, 152, 154, 155, 156, 157, 160, 161, 162, 164, 165, 166, 169, 173, 174, 177, 178, 179, 182, 183, 184, 185, 187, 191, 192, 193, 194, 195, 197, 198, 199, 200, 202, 205, 212, 214, 215, 216, 219, 220, 221, 225, 226, 228, 230}

def g32p_centralizerBound077_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (12, 7)}

theorem g32p_centralizerBound077_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) := by
  decide +kernel

theorem g32p_centralizerBound077_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 77) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound077_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound077_point_block00 t
  · exact g32p_centralizerBound077_point_block01 t
  · exact g32p_centralizerBound077_point_block02 t
  · exact g32p_centralizerBound077_point_block03 t
  · exact g32p_centralizerBound077_point_block04 t
  · exact g32p_centralizerBound077_point_block05 t
  · exact g32p_centralizerBound077_point_block06 t
  · exact g32p_centralizerBound077_point_block07 t
  · exact g32p_centralizerBound077_point_block08 t
  · exact g32p_centralizerBound077_point_block09 t
  · exact g32p_centralizerBound077_point_block10 t
  · exact g32p_centralizerBound077_point_block11 t
  · exact g32p_centralizerBound077_point_block12 t
  · exact g32p_centralizerBound077_point_block13 t
  · exact g32p_centralizerBound077_point_block14 t

theorem g32p_centralizerBound077_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 77) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 77)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound077_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound077_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 77) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 77)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound077_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound077_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 77) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 77)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound077_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound077_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 77) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 77)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound077_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound077_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 77) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 77)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound077_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound077_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 77) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 77) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound077_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 77) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 77)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound077_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound077_stabilizer_block00 t r
  · exact g32p_centralizerBound077_stabilizer_block01 t r
  · exact g32p_centralizerBound077_stabilizer_block02 t r
  · exact g32p_centralizerBound077_stabilizer_block03 t r
  · exact g32p_centralizerBound077_stabilizer_block04 t r

theorem g32p_centralizerBound077_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 77}) ≤ g32p_literalCentralizer 77 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 77 g32p_centralizerBound077_points
    g32p_centralizerBound077_stabilizers ?_ g32p_centralizerBound077_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound077_point_mem i (g32p_centralizer_point_moments 77 x i hi.symm)

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

def g32p_centralizerBound078_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 9, 11, 12, 14, 15, 16, 18, 20, 21, 24, 25, 27, 31, 33, 36, 38, 40, 42, 43, 46, 47, 49, 53, 55, 58, 62, 65, 66, 67, 70, 72, 75, 76, 78, 82, 83, 84, 87, 88, 90, 94, 96, 99, 103, 106, 107, 108, 111, 113, 116, 117, 119, 123, 124, 125, 129, 131, 136, 138, 139, 144, 146, 149, 152, 155, 156, 157, 160, 162, 165, 166, 168, 172, 173, 174, 177, 179, 184, 186, 187, 191, 193, 196, 197, 198, 200, 202, 204, 206, 207, 209, 211, 212, 214, 216, 219, 221, 225, 227, 228, 230, 233, 235}

def g32p_centralizerBound078_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (12, 7), (20, 4), (24, 1), (26, 2)}

theorem g32p_centralizerBound078_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) := by
  decide +kernel

theorem g32p_centralizerBound078_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 78) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound078_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound078_point_block00 t
  · exact g32p_centralizerBound078_point_block01 t
  · exact g32p_centralizerBound078_point_block02 t
  · exact g32p_centralizerBound078_point_block03 t
  · exact g32p_centralizerBound078_point_block04 t
  · exact g32p_centralizerBound078_point_block05 t
  · exact g32p_centralizerBound078_point_block06 t
  · exact g32p_centralizerBound078_point_block07 t
  · exact g32p_centralizerBound078_point_block08 t
  · exact g32p_centralizerBound078_point_block09 t
  · exact g32p_centralizerBound078_point_block10 t
  · exact g32p_centralizerBound078_point_block11 t
  · exact g32p_centralizerBound078_point_block12 t
  · exact g32p_centralizerBound078_point_block13 t
  · exact g32p_centralizerBound078_point_block14 t

theorem g32p_centralizerBound078_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 78) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 78)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound078_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound078_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 78) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 78)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound078_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound078_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 78) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 78)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound078_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound078_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 78) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 78)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound078_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound078_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 78) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 78)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound078_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound078_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 78) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 78) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound078_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 78) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 78)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound078_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound078_stabilizer_block00 t r
  · exact g32p_centralizerBound078_stabilizer_block01 t r
  · exact g32p_centralizerBound078_stabilizer_block02 t r
  · exact g32p_centralizerBound078_stabilizer_block03 t r
  · exact g32p_centralizerBound078_stabilizer_block04 t r

theorem g32p_centralizerBound078_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 78}) ≤ g32p_literalCentralizer 78 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 78 g32p_centralizerBound078_points
    g32p_centralizerBound078_stabilizers ?_ g32p_centralizerBound078_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound078_point_mem i (g32p_centralizer_point_moments 78 x i hi.symm)

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

def g32p_centralizerBound079_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 11, 12, 14, 15, 16, 20, 21, 24, 25, 26, 27, 28, 29, 30, 31, 36, 38, 42, 43, 46, 47, 48, 49, 50, 51, 52, 53, 58, 60, 61, 62, 66, 69, 70, 71, 73, 74, 76, 78, 79, 81, 82, 83, 84, 87, 88, 89, 90, 91, 92, 93, 94, 99, 101, 102, 103, 107, 110, 111, 112, 114, 115, 117, 119, 120, 122, 123, 124, 125, 127, 128, 129, 131, 132, 133, 134, 135, 137, 138, 142, 143, 145, 149, 150, 151, 152, 156, 159, 160, 161, 163, 164, 166, 168, 169, 171, 172, 173, 174, 176, 177, 179, 180, 181, 182, 183, 185, 186, 189, 190, 192, 196, 203, 204, 205, 206, 207, 209, 210, 211, 213, 214, 216, 217, 218, 220, 223, 224, 226, 227, 231, 233, 234, 235, 236, 237}

def g32p_centralizerBound079_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7)}

theorem g32p_centralizerBound079_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) := by
  decide +kernel

theorem g32p_centralizerBound079_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 79) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound079_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound079_point_block00 t
  · exact g32p_centralizerBound079_point_block01 t
  · exact g32p_centralizerBound079_point_block02 t
  · exact g32p_centralizerBound079_point_block03 t
  · exact g32p_centralizerBound079_point_block04 t
  · exact g32p_centralizerBound079_point_block05 t
  · exact g32p_centralizerBound079_point_block06 t
  · exact g32p_centralizerBound079_point_block07 t
  · exact g32p_centralizerBound079_point_block08 t
  · exact g32p_centralizerBound079_point_block09 t
  · exact g32p_centralizerBound079_point_block10 t
  · exact g32p_centralizerBound079_point_block11 t
  · exact g32p_centralizerBound079_point_block12 t
  · exact g32p_centralizerBound079_point_block13 t
  · exact g32p_centralizerBound079_point_block14 t

theorem g32p_centralizerBound079_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 79) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 79)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound079_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound079_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 79) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 79)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound079_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound079_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 79) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 79)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound079_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound079_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 79) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 79)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound079_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound079_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 79) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 79)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound079_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound079_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 79) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 79) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound079_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 79) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 79)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound079_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound079_stabilizer_block00 t r
  · exact g32p_centralizerBound079_stabilizer_block01 t r
  · exact g32p_centralizerBound079_stabilizer_block02 t r
  · exact g32p_centralizerBound079_stabilizer_block03 t r
  · exact g32p_centralizerBound079_stabilizer_block04 t r

theorem g32p_centralizerBound079_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 79}) ≤ g32p_literalCentralizer 79 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 79 g32p_centralizerBound079_points
    g32p_centralizerBound079_stabilizers ?_ g32p_centralizerBound079_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound079_point_mem i (g32p_centralizer_point_moments 79 x i hi.symm)

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

def g32p_centralizerBound080_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 11, 12, 14, 15, 20, 21, 24, 25, 27, 29, 36, 42, 43, 46, 47, 49, 51, 58, 60, 62, 74, 79, 82, 83, 84, 87, 88, 90, 92, 99, 101, 103, 115, 120, 123, 124, 125, 131, 135, 137, 138, 145, 149, 150, 152, 164, 169, 172, 173, 174, 179, 183, 185, 186, 192, 196, 205, 206, 207, 211, 216, 220, 226, 227, 235}

def g32p_centralizerBound080_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound080_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) := by
  decide +kernel

theorem g32p_centralizerBound080_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 80) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound080_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound080_point_block00 t
  · exact g32p_centralizerBound080_point_block01 t
  · exact g32p_centralizerBound080_point_block02 t
  · exact g32p_centralizerBound080_point_block03 t
  · exact g32p_centralizerBound080_point_block04 t
  · exact g32p_centralizerBound080_point_block05 t
  · exact g32p_centralizerBound080_point_block06 t
  · exact g32p_centralizerBound080_point_block07 t
  · exact g32p_centralizerBound080_point_block08 t
  · exact g32p_centralizerBound080_point_block09 t
  · exact g32p_centralizerBound080_point_block10 t
  · exact g32p_centralizerBound080_point_block11 t
  · exact g32p_centralizerBound080_point_block12 t
  · exact g32p_centralizerBound080_point_block13 t
  · exact g32p_centralizerBound080_point_block14 t

theorem g32p_centralizerBound080_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 80) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 80)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound080_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound080_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 80) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 80)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound080_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound080_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 80) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 80)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound080_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound080_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 80) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 80)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound080_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound080_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 80) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 80)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound080_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound080_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 80) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 80) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound080_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 80) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 80)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound080_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound080_stabilizer_block00 t r
  · exact g32p_centralizerBound080_stabilizer_block01 t r
  · exact g32p_centralizerBound080_stabilizer_block02 t r
  · exact g32p_centralizerBound080_stabilizer_block03 t r
  · exact g32p_centralizerBound080_stabilizer_block04 t r

theorem g32p_centralizerBound080_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 80}) ≤ g32p_literalCentralizer 80 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 80 g32p_centralizerBound080_points
    g32p_centralizerBound080_stabilizers ?_ g32p_centralizerBound080_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound080_point_mem i (g32p_centralizer_point_moments 80 x i hi.symm)

end HodgeLean.Foundations.Program

end
end
