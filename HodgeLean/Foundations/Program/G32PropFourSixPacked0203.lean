import HodgeLean.Foundations.Program.G32PropFourSixPacked0201
import HodgeLean.Foundations.Program.G32PropFourSixPacked0019

section

noncomputable section
namespace HodgeLean.Foundations.Program
open HodgeLean.Papers
set_option maxHeartbeats 400000
set_option maxRecDepth 2048
set_option backward.isDefEq.respectTransparency false

def g32p_centralizerBound032_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 11, 13, 14, 15, 16, 17, 20, 22, 23, 25, 28, 32, 35, 36, 38, 39, 42, 44, 45, 47, 50, 54, 57, 58, 64, 65, 66, 69, 73, 78, 79, 81, 83, 85, 86, 88, 91, 95, 98, 99, 105, 106, 107, 110, 114, 119, 120, 122, 124, 126, 127, 128, 130, 134, 136, 138, 140, 141, 145, 146, 148, 149, 154, 155, 156, 159, 163, 168, 169, 171, 173, 175, 176, 178, 182, 184, 186, 188, 192, 193, 195, 196, 198, 200, 203, 204, 206, 209, 210, 212, 213, 215, 219, 222, 226, 227, 228, 231, 233, 234, 236, 237}

def g32p_centralizerBound032_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (16, 2), (49, 4)}

theorem g32p_centralizerBound032_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) := by
  decide +kernel

theorem g32p_centralizerBound032_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 32) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound032_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound032_point_block00 t
  · exact g32p_centralizerBound032_point_block01 t
  · exact g32p_centralizerBound032_point_block02 t
  · exact g32p_centralizerBound032_point_block03 t
  · exact g32p_centralizerBound032_point_block04 t
  · exact g32p_centralizerBound032_point_block05 t
  · exact g32p_centralizerBound032_point_block06 t
  · exact g32p_centralizerBound032_point_block07 t
  · exact g32p_centralizerBound032_point_block08 t
  · exact g32p_centralizerBound032_point_block09 t
  · exact g32p_centralizerBound032_point_block10 t
  · exact g32p_centralizerBound032_point_block11 t
  · exact g32p_centralizerBound032_point_block12 t
  · exact g32p_centralizerBound032_point_block13 t
  · exact g32p_centralizerBound032_point_block14 t

theorem g32p_centralizerBound032_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 32) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 32)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound032_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound032_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 32) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 32)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound032_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound032_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 32) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 32)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound032_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound032_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 32) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 32)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound032_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound032_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 32) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 32)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound032_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound032_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 32) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 32) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound032_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 32) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 32)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound032_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound032_stabilizer_block00 t r
  · exact g32p_centralizerBound032_stabilizer_block01 t r
  · exact g32p_centralizerBound032_stabilizer_block02 t r
  · exact g32p_centralizerBound032_stabilizer_block03 t r
  · exact g32p_centralizerBound032_stabilizer_block04 t r

theorem g32p_centralizerBound032_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 32}) ≤ g32p_literalCentralizer 32 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 32 g32p_centralizerBound032_points
    g32p_centralizerBound032_stabilizers ?_ g32p_centralizerBound032_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound032_point_mem i (g32p_centralizer_point_moments 32 x i hi.symm)

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

def g32p_centralizerBound033_points : Finset (Fin 240) :=
  {3, 6, 7, 15, 16, 36, 38, 58, 63, 66, 80, 99, 104, 107, 121, 153, 156, 170}

def g32p_centralizerBound033_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (13, 5), (59, 1)}

theorem g32p_centralizerBound033_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) := by
  decide +kernel

theorem g32p_centralizerBound033_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 33) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound033_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound033_point_block00 t
  · exact g32p_centralizerBound033_point_block01 t
  · exact g32p_centralizerBound033_point_block02 t
  · exact g32p_centralizerBound033_point_block03 t
  · exact g32p_centralizerBound033_point_block04 t
  · exact g32p_centralizerBound033_point_block05 t
  · exact g32p_centralizerBound033_point_block06 t
  · exact g32p_centralizerBound033_point_block07 t
  · exact g32p_centralizerBound033_point_block08 t
  · exact g32p_centralizerBound033_point_block09 t
  · exact g32p_centralizerBound033_point_block10 t
  · exact g32p_centralizerBound033_point_block11 t
  · exact g32p_centralizerBound033_point_block12 t
  · exact g32p_centralizerBound033_point_block13 t
  · exact g32p_centralizerBound033_point_block14 t

theorem g32p_centralizerBound033_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 33) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 33)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound033_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound033_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 33) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 33)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound033_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound033_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 33) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 33)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound033_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound033_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 33) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 33)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound033_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound033_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 33) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 33)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound033_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound033_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 33) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 33) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound033_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 33) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 33)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound033_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound033_stabilizer_block00 t r
  · exact g32p_centralizerBound033_stabilizer_block01 t r
  · exact g32p_centralizerBound033_stabilizer_block02 t r
  · exact g32p_centralizerBound033_stabilizer_block03 t r
  · exact g32p_centralizerBound033_stabilizer_block04 t r

theorem g32p_centralizerBound033_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 33}) ≤ g32p_literalCentralizer 33 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 33 g32p_centralizerBound033_points
    g32p_centralizerBound033_stabilizers ?_ g32p_centralizerBound033_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound033_point_mem i (g32p_centralizer_point_moments 33 x i hi.symm)

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

def g32p_centralizerBound034_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 9, 10, 11, 12, 14, 15, 16, 18, 19, 20, 21, 24, 25, 33, 36, 38, 40, 41, 42, 43, 46, 47, 55, 58, 60, 63, 66, 67, 68, 80, 83, 84, 87, 88, 96, 99, 101, 104, 107, 108, 109, 121, 124, 125, 131, 133, 142, 144, 150, 153, 156, 157, 158, 170, 173, 174, 179, 181, 189, 191, 216, 218, 223, 225}

def g32p_centralizerBound034_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (26, 2), (53, 2), (70, 7)}

theorem g32p_centralizerBound034_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) := by
  decide +kernel

theorem g32p_centralizerBound034_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 34) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound034_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound034_point_block00 t
  · exact g32p_centralizerBound034_point_block01 t
  · exact g32p_centralizerBound034_point_block02 t
  · exact g32p_centralizerBound034_point_block03 t
  · exact g32p_centralizerBound034_point_block04 t
  · exact g32p_centralizerBound034_point_block05 t
  · exact g32p_centralizerBound034_point_block06 t
  · exact g32p_centralizerBound034_point_block07 t
  · exact g32p_centralizerBound034_point_block08 t
  · exact g32p_centralizerBound034_point_block09 t
  · exact g32p_centralizerBound034_point_block10 t
  · exact g32p_centralizerBound034_point_block11 t
  · exact g32p_centralizerBound034_point_block12 t
  · exact g32p_centralizerBound034_point_block13 t
  · exact g32p_centralizerBound034_point_block14 t

theorem g32p_centralizerBound034_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 34) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 34)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound034_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound034_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 34) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 34)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound034_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound034_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 34) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 34)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound034_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound034_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 34) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 34)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound034_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound034_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 34) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 34)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound034_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound034_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 34) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 34) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound034_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 34) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 34)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound034_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound034_stabilizer_block00 t r
  · exact g32p_centralizerBound034_stabilizer_block01 t r
  · exact g32p_centralizerBound034_stabilizer_block02 t r
  · exact g32p_centralizerBound034_stabilizer_block03 t r
  · exact g32p_centralizerBound034_stabilizer_block04 t r

theorem g32p_centralizerBound034_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 34}) ≤ g32p_literalCentralizer 34 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 34 g32p_centralizerBound034_points
    g32p_centralizerBound034_stabilizers ?_ g32p_centralizerBound034_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound034_point_mem i (g32p_centralizer_point_moments 34 x i hi.symm)

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

def g32p_centralizerBound035_points : Finset (Fin 240) :=
  {0, 1, 2, 3, 4, 5, 6, 7, 11, 14, 15, 16, 20, 25, 27, 30, 31, 36, 38, 42, 47, 49, 52, 53, 58, 60, 62, 66, 71, 74, 76, 83, 88, 90, 93, 94, 99, 101, 103, 107, 112, 115, 117, 124, 137, 150, 152, 156, 161, 164, 166, 173, 185, 220}

def g32p_centralizerBound035_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (12, 1), (18, 2), (31, 3), (59, 7), (68, 7)}

theorem g32p_centralizerBound035_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) := by
  decide +kernel

theorem g32p_centralizerBound035_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 35) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound035_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound035_point_block00 t
  · exact g32p_centralizerBound035_point_block01 t
  · exact g32p_centralizerBound035_point_block02 t
  · exact g32p_centralizerBound035_point_block03 t
  · exact g32p_centralizerBound035_point_block04 t
  · exact g32p_centralizerBound035_point_block05 t
  · exact g32p_centralizerBound035_point_block06 t
  · exact g32p_centralizerBound035_point_block07 t
  · exact g32p_centralizerBound035_point_block08 t
  · exact g32p_centralizerBound035_point_block09 t
  · exact g32p_centralizerBound035_point_block10 t
  · exact g32p_centralizerBound035_point_block11 t
  · exact g32p_centralizerBound035_point_block12 t
  · exact g32p_centralizerBound035_point_block13 t
  · exact g32p_centralizerBound035_point_block14 t

theorem g32p_centralizerBound035_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 35) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 35)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound035_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound035_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 35) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 35)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound035_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound035_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 35) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 35)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound035_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound035_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 35) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 35)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound035_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound035_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 35) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 35)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound035_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound035_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 35) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 35) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound035_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 35) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 35)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound035_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound035_stabilizer_block00 t r
  · exact g32p_centralizerBound035_stabilizer_block01 t r
  · exact g32p_centralizerBound035_stabilizer_block02 t r
  · exact g32p_centralizerBound035_stabilizer_block03 t r
  · exact g32p_centralizerBound035_stabilizer_block04 t r

theorem g32p_centralizerBound035_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 35}) ≤ g32p_literalCentralizer 35 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 35 g32p_centralizerBound035_points
    g32p_centralizerBound035_stabilizers ?_ g32p_centralizerBound035_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound035_point_mem i (g32p_centralizer_point_moments 35 x i hi.symm)

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

def g32p_centralizerBound036_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 12, 14, 15, 21, 25, 26, 27, 28, 36, 43, 47, 48, 49, 50, 58, 61, 62, 79, 84, 88, 89, 90, 91, 99, 102, 103, 120, 125, 127, 132, 133, 134, 142, 143, 145, 151, 152, 169, 174, 180, 181, 182, 189, 190, 192, 217, 218, 223, 224, 226}

def g32p_centralizerBound036_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound036_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) := by
  decide +kernel

theorem g32p_centralizerBound036_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 36) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound036_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound036_point_block00 t
  · exact g32p_centralizerBound036_point_block01 t
  · exact g32p_centralizerBound036_point_block02 t
  · exact g32p_centralizerBound036_point_block03 t
  · exact g32p_centralizerBound036_point_block04 t
  · exact g32p_centralizerBound036_point_block05 t
  · exact g32p_centralizerBound036_point_block06 t
  · exact g32p_centralizerBound036_point_block07 t
  · exact g32p_centralizerBound036_point_block08 t
  · exact g32p_centralizerBound036_point_block09 t
  · exact g32p_centralizerBound036_point_block10 t
  · exact g32p_centralizerBound036_point_block11 t
  · exact g32p_centralizerBound036_point_block12 t
  · exact g32p_centralizerBound036_point_block13 t
  · exact g32p_centralizerBound036_point_block14 t

theorem g32p_centralizerBound036_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 36) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 36)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound036_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound036_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 36) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 36)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound036_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound036_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 36) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 36)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound036_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound036_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 36) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 36)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound036_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound036_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 36) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 36)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound036_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound036_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 36) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 36) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound036_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 36) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 36)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound036_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound036_stabilizer_block00 t r
  · exact g32p_centralizerBound036_stabilizer_block01 t r
  · exact g32p_centralizerBound036_stabilizer_block02 t r
  · exact g32p_centralizerBound036_stabilizer_block03 t r
  · exact g32p_centralizerBound036_stabilizer_block04 t r

theorem g32p_centralizerBound036_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 36}) ≤ g32p_literalCentralizer 36 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 36 g32p_centralizerBound036_points
    g32p_centralizerBound036_stabilizers ?_ g32p_centralizerBound036_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound036_point_mem i (g32p_centralizer_point_moments 36 x i hi.symm)

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

def g32p_centralizerBound038_points : Finset (Fin 240) :=
  {3, 6, 15, 27, 36, 49, 58, 62, 65, 75, 90, 99, 103, 106, 116, 139, 152, 155, 165, 187, 200, 212, 221, 228}

def g32p_centralizerBound038_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound038_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) := by
  decide +kernel

theorem g32p_centralizerBound038_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 38) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound038_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound038_point_block00 t
  · exact g32p_centralizerBound038_point_block01 t
  · exact g32p_centralizerBound038_point_block02 t
  · exact g32p_centralizerBound038_point_block03 t
  · exact g32p_centralizerBound038_point_block04 t
  · exact g32p_centralizerBound038_point_block05 t
  · exact g32p_centralizerBound038_point_block06 t
  · exact g32p_centralizerBound038_point_block07 t
  · exact g32p_centralizerBound038_point_block08 t
  · exact g32p_centralizerBound038_point_block09 t
  · exact g32p_centralizerBound038_point_block10 t
  · exact g32p_centralizerBound038_point_block11 t
  · exact g32p_centralizerBound038_point_block12 t
  · exact g32p_centralizerBound038_point_block13 t
  · exact g32p_centralizerBound038_point_block14 t

theorem g32p_centralizerBound038_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 38) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 38)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound038_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound038_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 38) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 38)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound038_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound038_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 38) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 38)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound038_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound038_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 38) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 38)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound038_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound038_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 38) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 38)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound038_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound038_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 38) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 38) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound038_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 38) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 38)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound038_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound038_stabilizer_block00 t r
  · exact g32p_centralizerBound038_stabilizer_block01 t r
  · exact g32p_centralizerBound038_stabilizer_block02 t r
  · exact g32p_centralizerBound038_stabilizer_block03 t r
  · exact g32p_centralizerBound038_stabilizer_block04 t r

theorem g32p_centralizerBound038_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 38}) ≤ g32p_literalCentralizer 38 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 38 g32p_centralizerBound038_points
    g32p_centralizerBound038_stabilizers ?_ g32p_centralizerBound038_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound038_point_mem i (g32p_centralizer_point_moments 38 x i hi.symm)

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

def g32p_centralizerBound039_points : Finset (Fin 240) :=
  {3, 6, 15, 26, 30, 31, 36, 48, 52, 53, 58, 61, 63, 64, 65, 71, 75, 76, 80, 85, 89, 93, 94, 99, 102, 104, 105, 106, 112, 116, 117, 121, 126, 130, 139, 140, 151, 153, 154, 155, 161, 165, 166, 170, 175, 178, 187, 188, 200, 212, 215, 221, 222, 228}

def g32p_centralizerBound039_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound039_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) := by
  decide +kernel

theorem g32p_centralizerBound039_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 39) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound039_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound039_point_block00 t
  · exact g32p_centralizerBound039_point_block01 t
  · exact g32p_centralizerBound039_point_block02 t
  · exact g32p_centralizerBound039_point_block03 t
  · exact g32p_centralizerBound039_point_block04 t
  · exact g32p_centralizerBound039_point_block05 t
  · exact g32p_centralizerBound039_point_block06 t
  · exact g32p_centralizerBound039_point_block07 t
  · exact g32p_centralizerBound039_point_block08 t
  · exact g32p_centralizerBound039_point_block09 t
  · exact g32p_centralizerBound039_point_block10 t
  · exact g32p_centralizerBound039_point_block11 t
  · exact g32p_centralizerBound039_point_block12 t
  · exact g32p_centralizerBound039_point_block13 t
  · exact g32p_centralizerBound039_point_block14 t

theorem g32p_centralizerBound039_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 39) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 39)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound039_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound039_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 39) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 39)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound039_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound039_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 39) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 39)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound039_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound039_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 39) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 39)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound039_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound039_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 39) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 39)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound039_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound039_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 39) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 39) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound039_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 39) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 39)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound039_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound039_stabilizer_block00 t r
  · exact g32p_centralizerBound039_stabilizer_block01 t r
  · exact g32p_centralizerBound039_stabilizer_block02 t r
  · exact g32p_centralizerBound039_stabilizer_block03 t r
  · exact g32p_centralizerBound039_stabilizer_block04 t r

theorem g32p_centralizerBound039_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 39}) ≤ g32p_literalCentralizer 39 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 39 g32p_centralizerBound039_points
    g32p_centralizerBound039_stabilizers ?_ g32p_centralizerBound039_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound039_point_mem i (g32p_centralizer_point_moments 39 x i hi.symm)

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

def g32p_centralizerBound040_points : Finset (Fin 240) :=
  {3, 6, 15, 33, 36, 55, 58, 85, 96, 99, 126, 140, 144, 175, 188, 191, 222, 225}

def g32p_centralizerBound040_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (12, 0), (24, 2), (26, 2), (53, 8), (70, 0)}

theorem g32p_centralizerBound040_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) := by
  decide +kernel

theorem g32p_centralizerBound040_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 40) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound040_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound040_point_block00 t
  · exact g32p_centralizerBound040_point_block01 t
  · exact g32p_centralizerBound040_point_block02 t
  · exact g32p_centralizerBound040_point_block03 t
  · exact g32p_centralizerBound040_point_block04 t
  · exact g32p_centralizerBound040_point_block05 t
  · exact g32p_centralizerBound040_point_block06 t
  · exact g32p_centralizerBound040_point_block07 t
  · exact g32p_centralizerBound040_point_block08 t
  · exact g32p_centralizerBound040_point_block09 t
  · exact g32p_centralizerBound040_point_block10 t
  · exact g32p_centralizerBound040_point_block11 t
  · exact g32p_centralizerBound040_point_block12 t
  · exact g32p_centralizerBound040_point_block13 t
  · exact g32p_centralizerBound040_point_block14 t

theorem g32p_centralizerBound040_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 40) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 40)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound040_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound040_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 40) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 40)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound040_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound040_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 40) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 40)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound040_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound040_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 40) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 40)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound040_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound040_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 40) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 40)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound040_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound040_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 40) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 40) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound040_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 40) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 40)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound040_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound040_stabilizer_block00 t r
  · exact g32p_centralizerBound040_stabilizer_block01 t r
  · exact g32p_centralizerBound040_stabilizer_block02 t r
  · exact g32p_centralizerBound040_stabilizer_block03 t r
  · exact g32p_centralizerBound040_stabilizer_block04 t r

theorem g32p_centralizerBound040_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 40}) ≤ g32p_literalCentralizer 40 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 40 g32p_centralizerBound040_points
    g32p_centralizerBound040_stabilizers ?_ g32p_centralizerBound040_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound040_point_mem i (g32p_centralizer_point_moments 40 x i hi.symm)

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

def g32p_centralizerBound041_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 11, 12, 13, 14, 15, 16, 17, 18, 20, 21, 22, 23, 24, 25, 26, 32, 33, 36, 37, 38, 39, 40, 42, 43, 44, 45, 46, 47, 48, 54, 55, 58, 59, 61, 66, 67, 77, 83, 84, 86, 87, 88, 89, 95, 96, 99, 100, 102, 107, 108, 118, 124, 125, 131, 144, 151, 156, 157, 167, 173, 174, 179, 191, 216, 225}

def g32p_centralizerBound041_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound041_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) := by
  decide +kernel

theorem g32p_centralizerBound041_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 41) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound041_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound041_point_block00 t
  · exact g32p_centralizerBound041_point_block01 t
  · exact g32p_centralizerBound041_point_block02 t
  · exact g32p_centralizerBound041_point_block03 t
  · exact g32p_centralizerBound041_point_block04 t
  · exact g32p_centralizerBound041_point_block05 t
  · exact g32p_centralizerBound041_point_block06 t
  · exact g32p_centralizerBound041_point_block07 t
  · exact g32p_centralizerBound041_point_block08 t
  · exact g32p_centralizerBound041_point_block09 t
  · exact g32p_centralizerBound041_point_block10 t
  · exact g32p_centralizerBound041_point_block11 t
  · exact g32p_centralizerBound041_point_block12 t
  · exact g32p_centralizerBound041_point_block13 t
  · exact g32p_centralizerBound041_point_block14 t

theorem g32p_centralizerBound041_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 41) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 41)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound041_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound041_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 41) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 41)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound041_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound041_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 41) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 41)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound041_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound041_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 41) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 41)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound041_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound041_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 41) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 41)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound041_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound041_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 41) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 41) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound041_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 41) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 41)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound041_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound041_stabilizer_block00 t r
  · exact g32p_centralizerBound041_stabilizer_block01 t r
  · exact g32p_centralizerBound041_stabilizer_block02 t r
  · exact g32p_centralizerBound041_stabilizer_block03 t r
  · exact g32p_centralizerBound041_stabilizer_block04 t r

theorem g32p_centralizerBound041_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 41}) ≤ g32p_literalCentralizer 41 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 41 g32p_centralizerBound041_points
    g32p_centralizerBound041_stabilizers ?_ g32p_centralizerBound041_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound041_point_mem i (g32p_centralizer_point_moments 41 x i hi.symm)

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

def g32p_centralizerBound042_points : Finset (Fin 240) :=
  {3, 6, 15, 26, 31, 36, 37, 48, 53, 58, 59, 61, 63, 69, 74, 76, 77, 80, 81, 89, 94, 99, 100, 102, 104, 110, 115, 117, 118, 121, 122, 128, 133, 137, 142, 151, 153, 159, 164, 166, 167, 170, 171, 176, 181, 185, 189, 210, 213, 218, 220, 223, 234, 236}

def g32p_centralizerBound042_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound042_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) := by
  decide +kernel

theorem g32p_centralizerBound042_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 42) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound042_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound042_point_block00 t
  · exact g32p_centralizerBound042_point_block01 t
  · exact g32p_centralizerBound042_point_block02 t
  · exact g32p_centralizerBound042_point_block03 t
  · exact g32p_centralizerBound042_point_block04 t
  · exact g32p_centralizerBound042_point_block05 t
  · exact g32p_centralizerBound042_point_block06 t
  · exact g32p_centralizerBound042_point_block07 t
  · exact g32p_centralizerBound042_point_block08 t
  · exact g32p_centralizerBound042_point_block09 t
  · exact g32p_centralizerBound042_point_block10 t
  · exact g32p_centralizerBound042_point_block11 t
  · exact g32p_centralizerBound042_point_block12 t
  · exact g32p_centralizerBound042_point_block13 t
  · exact g32p_centralizerBound042_point_block14 t

theorem g32p_centralizerBound042_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 42) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 42)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound042_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound042_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 42) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 42)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound042_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound042_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 42) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 42)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound042_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound042_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 42) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 42)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound042_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound042_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 42) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 42)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound042_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound042_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 42) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 42) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound042_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 42) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 42)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound042_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound042_stabilizer_block00 t r
  · exact g32p_centralizerBound042_stabilizer_block01 t r
  · exact g32p_centralizerBound042_stabilizer_block02 t r
  · exact g32p_centralizerBound042_stabilizer_block03 t r
  · exact g32p_centralizerBound042_stabilizer_block04 t r

theorem g32p_centralizerBound042_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 42}) ≤ g32p_literalCentralizer 42 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 42 g32p_centralizerBound042_points
    g32p_centralizerBound042_stabilizers ?_ g32p_centralizerBound042_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound042_point_mem i (g32p_centralizer_point_moments 42 x i hi.symm)

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

def g32p_centralizerBound043_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 11, 14, 15, 16, 20, 25, 27, 28, 29, 31, 34, 35, 36, 38, 42, 47, 49, 50, 51, 53, 56, 57, 58, 62, 64, 65, 66, 72, 76, 78, 79, 82, 83, 88, 90, 91, 92, 94, 97, 98, 99, 103, 105, 106, 107, 113, 117, 119, 120, 123, 124, 127, 130, 134, 135, 136, 138, 141, 145, 146, 147, 148, 149, 152, 154, 155, 156, 162, 166, 168, 169, 172, 173, 178, 182, 183, 184, 186, 192, 193, 194, 195, 196, 197, 198, 199, 200, 202, 204, 205, 206, 207, 209, 211, 212, 215, 219, 226, 227, 228, 230, 233, 235}

def g32p_centralizerBound043_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound043_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) := by
  decide +kernel

theorem g32p_centralizerBound043_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 43) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound043_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound043_point_block00 t
  · exact g32p_centralizerBound043_point_block01 t
  · exact g32p_centralizerBound043_point_block02 t
  · exact g32p_centralizerBound043_point_block03 t
  · exact g32p_centralizerBound043_point_block04 t
  · exact g32p_centralizerBound043_point_block05 t
  · exact g32p_centralizerBound043_point_block06 t
  · exact g32p_centralizerBound043_point_block07 t
  · exact g32p_centralizerBound043_point_block08 t
  · exact g32p_centralizerBound043_point_block09 t
  · exact g32p_centralizerBound043_point_block10 t
  · exact g32p_centralizerBound043_point_block11 t
  · exact g32p_centralizerBound043_point_block12 t
  · exact g32p_centralizerBound043_point_block13 t
  · exact g32p_centralizerBound043_point_block14 t

theorem g32p_centralizerBound043_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 43) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 43)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound043_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound043_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 43) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 43)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound043_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound043_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 43) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 43)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound043_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound043_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 43) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 43)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound043_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound043_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 43) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 43)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound043_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound043_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 43) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 43) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound043_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 43) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 43)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound043_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound043_stabilizer_block00 t r
  · exact g32p_centralizerBound043_stabilizer_block01 t r
  · exact g32p_centralizerBound043_stabilizer_block02 t r
  · exact g32p_centralizerBound043_stabilizer_block03 t r
  · exact g32p_centralizerBound043_stabilizer_block04 t r

theorem g32p_centralizerBound043_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 43}) ≤ g32p_literalCentralizer 43 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 43 g32p_centralizerBound043_points
    g32p_centralizerBound043_stabilizers ?_ g32p_centralizerBound043_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound043_point_mem i (g32p_centralizer_point_moments 43 x i hi.symm)

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

def g32p_centralizerBound044_points : Finset (Fin 240) :=
  {2, 3, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 30, 32, 33, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 50, 52, 54, 55, 57, 58, 59, 61, 64, 65, 66, 67, 68, 69, 71, 73, 74, 77, 78, 79, 81, 83, 84, 85, 86, 87, 88, 89, 91, 93, 95, 96, 98, 99, 100, 102, 105, 106, 107, 108, 109, 110, 112, 114, 115, 118, 119, 120, 122, 124, 125, 126, 127, 128, 130, 131, 134, 136, 137, 138, 140, 141, 144, 145, 146, 148, 149, 151, 154, 155, 156, 157, 158, 159, 161, 163, 164, 167, 168, 169, 171, 173, 174, 175, 176, 178, 179, 182, 184, 185, 186, 188, 191, 192, 193, 195, 196, 198, 200, 203, 204, 206, 209, 210, 212, 213, 215, 216, 219, 220, 222, 225, 226, 227, 228, 231, 233, 234, 236, 237}

def g32p_centralizerBound044_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (0, 6), (0, 7), (8, 3), (8, 4), (8, 5), (10, 3), (10, 4), (10, 5), (16, 1), (16, 2), (16, 8), (18, 1), (18, 2), (18, 8), (49, 3), (49, 4), (49, 5), (60, 3), (60, 4), (60, 5), (68, 0), (68, 6), (68, 7)}

theorem g32p_centralizerBound044_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) := by
  decide +kernel

theorem g32p_centralizerBound044_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 44) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound044_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound044_point_block00 t
  · exact g32p_centralizerBound044_point_block01 t
  · exact g32p_centralizerBound044_point_block02 t
  · exact g32p_centralizerBound044_point_block03 t
  · exact g32p_centralizerBound044_point_block04 t
  · exact g32p_centralizerBound044_point_block05 t
  · exact g32p_centralizerBound044_point_block06 t
  · exact g32p_centralizerBound044_point_block07 t
  · exact g32p_centralizerBound044_point_block08 t
  · exact g32p_centralizerBound044_point_block09 t
  · exact g32p_centralizerBound044_point_block10 t
  · exact g32p_centralizerBound044_point_block11 t
  · exact g32p_centralizerBound044_point_block12 t
  · exact g32p_centralizerBound044_point_block13 t
  · exact g32p_centralizerBound044_point_block14 t

theorem g32p_centralizerBound044_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 44) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 44)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound044_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound044_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 44) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 44)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound044_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound044_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 44) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 44)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound044_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound044_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 44) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 44)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound044_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound044_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 44) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 44)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound044_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound044_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 44) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 44) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound044_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 44) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 44)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound044_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound044_stabilizer_block00 t r
  · exact g32p_centralizerBound044_stabilizer_block01 t r
  · exact g32p_centralizerBound044_stabilizer_block02 t r
  · exact g32p_centralizerBound044_stabilizer_block03 t r
  · exact g32p_centralizerBound044_stabilizer_block04 t r

theorem g32p_centralizerBound044_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 44}) ≤ g32p_literalCentralizer 44 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 44 g32p_centralizerBound044_points
    g32p_centralizerBound044_stabilizers ?_ g32p_centralizerBound044_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound044_point_mem i (g32p_centralizer_point_moments 44 x i hi.symm)

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

def g32p_centralizerBound045_points : Finset (Fin 240) :=
  {3, 6, 10, 15, 19, 27, 33, 36, 41, 49, 55, 58, 62, 68, 75, 78, 85, 90, 96, 99, 103, 109, 116, 119, 126, 133, 138, 139, 140, 142, 144, 149, 152, 158, 165, 168, 175, 181, 186, 187, 188, 189, 191, 196, 204, 206, 209, 218, 221, 222, 223, 225, 227, 233}

def g32p_centralizerBound045_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (1, 3), (12, 7), (20, 4), (24, 1), (26, 2)}

theorem g32p_centralizerBound045_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) := by
  decide +kernel

theorem g32p_centralizerBound045_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 45) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound045_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound045_point_block00 t
  · exact g32p_centralizerBound045_point_block01 t
  · exact g32p_centralizerBound045_point_block02 t
  · exact g32p_centralizerBound045_point_block03 t
  · exact g32p_centralizerBound045_point_block04 t
  · exact g32p_centralizerBound045_point_block05 t
  · exact g32p_centralizerBound045_point_block06 t
  · exact g32p_centralizerBound045_point_block07 t
  · exact g32p_centralizerBound045_point_block08 t
  · exact g32p_centralizerBound045_point_block09 t
  · exact g32p_centralizerBound045_point_block10 t
  · exact g32p_centralizerBound045_point_block11 t
  · exact g32p_centralizerBound045_point_block12 t
  · exact g32p_centralizerBound045_point_block13 t
  · exact g32p_centralizerBound045_point_block14 t

theorem g32p_centralizerBound045_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 45) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 45)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound045_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound045_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 45) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 45)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound045_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound045_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 45) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 45)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound045_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound045_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 45) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 45)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound045_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound045_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 45) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 45)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound045_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound045_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 45) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 45) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound045_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 45) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 45)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound045_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound045_stabilizer_block00 t r
  · exact g32p_centralizerBound045_stabilizer_block01 t r
  · exact g32p_centralizerBound045_stabilizer_block02 t r
  · exact g32p_centralizerBound045_stabilizer_block03 t r
  · exact g32p_centralizerBound045_stabilizer_block04 t r

theorem g32p_centralizerBound045_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 45}) ≤ g32p_literalCentralizer 45 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 45 g32p_centralizerBound045_points
    g32p_centralizerBound045_stabilizers ?_ g32p_centralizerBound045_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound045_point_mem i (g32p_centralizer_point_moments 45 x i hi.symm)

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

def g32p_centralizerBound046_points : Finset (Fin 240) :=
  {0, 1, 3, 4, 6, 7, 8, 15, 16, 17, 23, 26, 36, 38, 39, 45, 48, 58, 60, 61, 65, 66, 86, 89, 99, 101, 102, 106, 107, 150, 151, 155, 156, 200, 212, 228}

def g32p_centralizerBound046_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound046_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) := by
  decide +kernel

theorem g32p_centralizerBound046_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 46) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound046_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound046_point_block00 t
  · exact g32p_centralizerBound046_point_block01 t
  · exact g32p_centralizerBound046_point_block02 t
  · exact g32p_centralizerBound046_point_block03 t
  · exact g32p_centralizerBound046_point_block04 t
  · exact g32p_centralizerBound046_point_block05 t
  · exact g32p_centralizerBound046_point_block06 t
  · exact g32p_centralizerBound046_point_block07 t
  · exact g32p_centralizerBound046_point_block08 t
  · exact g32p_centralizerBound046_point_block09 t
  · exact g32p_centralizerBound046_point_block10 t
  · exact g32p_centralizerBound046_point_block11 t
  · exact g32p_centralizerBound046_point_block12 t
  · exact g32p_centralizerBound046_point_block13 t
  · exact g32p_centralizerBound046_point_block14 t

theorem g32p_centralizerBound046_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 46) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 46)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound046_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound046_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 46) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 46)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound046_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound046_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 46) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 46)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound046_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound046_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 46) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 46)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound046_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound046_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 46) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 46)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound046_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound046_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 46) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 46) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound046_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 46) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 46)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound046_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound046_stabilizer_block00 t r
  · exact g32p_centralizerBound046_stabilizer_block01 t r
  · exact g32p_centralizerBound046_stabilizer_block02 t r
  · exact g32p_centralizerBound046_stabilizer_block03 t r
  · exact g32p_centralizerBound046_stabilizer_block04 t r

theorem g32p_centralizerBound046_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 46}) ≤ g32p_literalCentralizer 46 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 46 g32p_centralizerBound046_points
    g32p_centralizerBound046_stabilizers ?_ g32p_centralizerBound046_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound046_point_mem i (g32p_centralizer_point_moments 46 x i hi.symm)

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

def g32p_centralizerBound047_points : Finset (Fin 240) :=
  {3, 6, 15, 34, 36, 56, 58, 64, 75, 97, 99, 105, 116, 130, 133, 139, 142, 147, 154, 165, 178, 181, 187, 189, 194, 199, 215, 218, 221, 223}

def g32p_centralizerBound047_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0)}

theorem g32p_centralizerBound047_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) := by
  decide +kernel

theorem g32p_centralizerBound047_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 47) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound047_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound047_point_block00 t
  · exact g32p_centralizerBound047_point_block01 t
  · exact g32p_centralizerBound047_point_block02 t
  · exact g32p_centralizerBound047_point_block03 t
  · exact g32p_centralizerBound047_point_block04 t
  · exact g32p_centralizerBound047_point_block05 t
  · exact g32p_centralizerBound047_point_block06 t
  · exact g32p_centralizerBound047_point_block07 t
  · exact g32p_centralizerBound047_point_block08 t
  · exact g32p_centralizerBound047_point_block09 t
  · exact g32p_centralizerBound047_point_block10 t
  · exact g32p_centralizerBound047_point_block11 t
  · exact g32p_centralizerBound047_point_block12 t
  · exact g32p_centralizerBound047_point_block13 t
  · exact g32p_centralizerBound047_point_block14 t

theorem g32p_centralizerBound047_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 47) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 47)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound047_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound047_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 47) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 47)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound047_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound047_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 47) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 47)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound047_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound047_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 47) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 47)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound047_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound047_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 47) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 47)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound047_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound047_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 47) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 47) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound047_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 47) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 47)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound047_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound047_stabilizer_block00 t r
  · exact g32p_centralizerBound047_stabilizer_block01 t r
  · exact g32p_centralizerBound047_stabilizer_block02 t r
  · exact g32p_centralizerBound047_stabilizer_block03 t r
  · exact g32p_centralizerBound047_stabilizer_block04 t r

theorem g32p_centralizerBound047_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 47}) ≤ g32p_literalCentralizer 47 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 47 g32p_centralizerBound047_points
    g32p_centralizerBound047_stabilizers ?_ g32p_centralizerBound047_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound047_point_mem i (g32p_centralizer_point_moments 47 x i hi.symm)

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

def g32p_centralizerBound048_points : Finset (Fin 240) :=
  {3, 6, 15, 31, 36, 37, 53, 58, 59, 76, 77, 81, 94, 99, 100, 117, 118, 122, 166, 167, 171, 210, 234, 236}

def g32p_centralizerBound048_stabilizers : Finset (Fin HurwitzPrymRex_g32TTwo.length ×
    Fin HurwitzPrymRex_g32TThree.length) :=
  {(0, 0), (7, 8), (27, 4)}

theorem g32p_centralizerBound048_point_block00 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 0 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block01 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 1 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block02 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 2 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block03 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 3 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block04 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 4 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block05 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 5 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block06 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 6 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block07 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 7 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block08 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 8 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block09 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 9 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block10 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 10 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block11 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 11 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block12 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 12 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block13 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 13 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_block14 : ∀ t : Fin 16,
    (let i := g32p_finBlockIndex 240 14 t;
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) := by
  decide +kernel

theorem g32p_centralizerBound048_point_mem (i : Fin 240) :
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points := by
  apply g32p_forall_fin_blocks (fun i =>
    g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix i) =
      g32p_pointMoments (g32p_literalRepresentativeMatrix 48) (g32p_rootMatrix 58) →
    i ∈ g32p_centralizerBound048_points) ?_ i
  intro q t
  fin_cases q
  · exact g32p_centralizerBound048_point_block00 t
  · exact g32p_centralizerBound048_point_block01 t
  · exact g32p_centralizerBound048_point_block02 t
  · exact g32p_centralizerBound048_point_block03 t
  · exact g32p_centralizerBound048_point_block04 t
  · exact g32p_centralizerBound048_point_block05 t
  · exact g32p_centralizerBound048_point_block06 t
  · exact g32p_centralizerBound048_point_block07 t
  · exact g32p_centralizerBound048_point_block08 t
  · exact g32p_centralizerBound048_point_block09 t
  · exact g32p_centralizerBound048_point_block10 t
  · exact g32p_centralizerBound048_point_block11 t
  · exact g32p_centralizerBound048_point_block12 t
  · exact g32p_centralizerBound048_point_block13 t
  · exact g32p_centralizerBound048_point_block14 t

theorem g32p_centralizerBound048_stabilizer_block00 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 0 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 48) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 48)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound048_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound048_stabilizer_block01 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 1 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 48) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 48)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound048_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound048_stabilizer_block02 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 2 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 48) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 48)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound048_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound048_stabilizer_block03 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 3 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 48) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 48)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound048_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound048_stabilizer_block04 : ∀ (t : Fin 16) (r : Fin 9),
    (let q := g32p_finBlockIndex 72 4 t;
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 48) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 48)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound048_stabilizers) := by
  decide +kernel

theorem g32p_centralizerBound048_stabilizer_mem
    (p : Fin HurwitzPrymRex_g32TTwo.length × Fin HurwitzPrymRex_g32TThree.length) :
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral p) (g32p_literalRepresentativeMatrix 48) =
      HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 48) (g32p_pointStabilizerIntegral p) →
      p ∈ g32p_centralizerBound048_stabilizers := by
  rcases p with ⟨q, r⟩
  apply g32p_forall_fin_blocks (fun q : Fin 72 =>
    HurwitzPrymRex_mmul (g32p_pointStabilizerIntegral (q, r))
      (g32p_literalRepresentativeMatrix 48) =
        HurwitzPrymRex_mmul (g32p_literalRepresentativeMatrix 48)
          (g32p_pointStabilizerIntegral (q, r)) → (q, r) ∈ g32p_centralizerBound048_stabilizers) ?_ q
  intro b t
  fin_cases b
  · exact g32p_centralizerBound048_stabilizer_block00 t r
  · exact g32p_centralizerBound048_stabilizer_block01 t r
  · exact g32p_centralizerBound048_stabilizer_block02 t r
  · exact g32p_centralizerBound048_stabilizer_block03 t r
  · exact g32p_centralizerBound048_stabilizer_block04 t r

theorem g32p_centralizerBound048_actual :
    Nat.card (Subgroup.centralizer {g32p_literalRepresentative 48}) ≤ g32p_literalCentralizer 48 := by
  apply le_trans (g32p_centralizer_card_le_of_index_codes 48 g32p_centralizerBound048_points
    g32p_centralizerBound048_stabilizers ?_ g32p_centralizerBound048_stabilizer_mem)
  · decide +kernel
  · intro x
    obtain ⟨i, hi⟩ := g32p_rootPoint_invariant (x : g32p_G) g32p_basePoint
      ⟨58, g32p_basePoint_root.symm⟩
    refine ⟨i, ?_, hi.symm⟩
    apply g32p_centralizerBound048_point_mem i (g32p_centralizer_point_moments 48 x i hi.symm)

end HodgeLean.Foundations.Program

end
end
