import Clifford.Basic

/-!
# Clifford's second and third circle theorems (n = 5, n = 6)

Continuation of `Clifford/Basic.lean`; same conventions (common point `M = 0` of `ℂ`, conjugate
coordinates `dᵢ` for `conj cᵢ` in the generic algebra over a field `K`).

## n = 5
Write `P_k` for the Clifford point (`XN / NN`) of the four circles other than circle `k`.  The key
identity (`cross`) is
  `XN_k NN_l - NN_k XN_l = dᵢ dⱼ dₘ LL_{ijm} · WW`        (`{i, j, m} = {1..5} \ {k, l}`)
with a *single* 5 × 5 determinant `WW` (rows `(cᵢ, dᵢ, cᵢdᵢ, dᵢ², cᵢ²)`), independent of `k, l`.
Hence `P_k - P_l` factors, and the concyclicity polynomial `TT` of any four of the points vanishes
by `ring` on opaque atoms.  If `WW = 0` all five points coincide; otherwise they are pairwise distinct,
and they are either concyclic or collinear (the n = 5 configuration may degenerate to a line).

## n = 6
The common point of the six circles `C_S` is `Q = ZN / ZD`, where `ZD`, `ZN` are the 6 × 6
determinants with rows `(dᵢ², dᵢ³, cᵢdᵢ, cᵢdᵢ², cᵢ²dᵢ, cᵢ²)` resp. `(…, cᵢ³)`, stored as their Laplace
expansions in the 5 × 5 minors `WW`.  The identity (`master`)
  `XN₁₂₃₄ ZD - NN₁₂₃₄ ZN = d₁d₂d₃d₄ · WW₁₂₃₄₅ · WW₁₂₃₄₆ · ee₅₆`
is proved by `linear_combination` from the cofactor expansion `cof_WW` and the vanishing Laplace sums
`lap_*`; it makes `P_T - Q` factor, so `TT(P, P', P'', Q) = 0` by `ring` on atoms (`TT_Q`).
`ZD ≠ 0` (`ZD_ne_zero`): if `ZD = 0`, then `master` forces `ZN = 0` (`den3_of_ZD`, using that `C_S` is
a genuine circle), and then `master` contradicts `WW ≠ 0`, `ee₅₆ ≠ 0`.
Non-degeneracy hypothesis of `clifford_three`: for every 5-subset, three of its Clifford points are
not collinear (so that `C_S` is a genuine circle, cf. the line case of `clifford_two`).
-/

open EuclideanGeometry ComplexConjugate

namespace Clifford

section Generic

variable {K : Type*} [Field K]

/-- The 5 × 5 determinant with rows `(cᵢ, dᵢ, cᵢ dᵢ, dᵢ², cᵢ²)`. -/
def WW (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) : K :=
    c1*c2*d1*d3*c5*c5*d4*d4 + c1*c2*d1*d4*c3*c3*d5*d5 + c1*c2*d1*d5*c4*c4*d3*d3 + c1*c2*d2*d3*c4*c4*d5*d5 + c1*c2*d2*d4*c5*c5*d3*d3 + c1*c2*d2*d5*c3*c3*d4*d4
    + c1*c3*d1*d2*c4*c4*d5*d5 + c1*c3*d1*d4*c5*c5*d2*d2 + c1*c3*d1*d5*c2*c2*d4*d4 + c1*c3*d2*d3*c5*c5*d4*d4 + c1*c3*d3*d4*c2*c2*d5*d5 + c1*c3*d3*d5*c4*c4*d2*d2
    + c1*c4*d1*d2*c5*c5*d3*d3 + c1*c4*d1*d3*c2*c2*d5*d5 + c1*c4*d1*d5*c3*c3*d2*d2 + c1*c4*d2*d4*c3*c3*d5*d5 + c1*c4*d3*d4*c5*c5*d2*d2 + c1*c4*d4*d5*c2*c2*d3*d3
    + c1*c5*d1*d2*c3*c3*d4*d4 + c1*c5*d1*d3*c4*c4*d2*d2 + c1*c5*d1*d4*c2*c2*d3*d3 + c1*c5*d2*d5*c4*c4*d3*d3 + c1*c5*d3*d5*c2*c2*d4*d4 + c1*c5*d4*d5*c3*c3*d2*d2
    + c2*c3*d1*d2*c5*c5*d4*d4 + c2*c3*d1*d3*c4*c4*d5*d5 + c2*c3*d2*d4*c1*c1*d5*d5 + c2*c3*d2*d5*c4*c4*d1*d1 + c2*c3*d3*d4*c5*c5*d1*d1 + c2*c3*d3*d5*c1*c1*d4*d4
    + c2*c4*d1*d2*c3*c3*d5*d5 + c2*c4*d1*d4*c5*c5*d3*d3 + c2*c4*d2*d3*c5*c5*d1*d1 + c2*c4*d2*d5*c1*c1*d3*d3 + c2*c4*d3*d4*c1*c1*d5*d5 + c2*c4*d4*d5*c3*c3*d1*d1
    + c2*c5*d1*d2*c4*c4*d3*d3 + c2*c5*d1*d5*c3*c3*d4*d4 + c2*c5*d2*d3*c1*c1*d4*d4 + c2*c5*d2*d4*c3*c3*d1*d1 + c2*c5*d3*d5*c4*c4*d1*d1 + c2*c5*d4*d5*c1*c1*d3*d3
    + c3*c4*d1*d3*c5*c5*d2*d2 + c3*c4*d1*d4*c2*c2*d5*d5 + c3*c4*d2*d3*c1*c1*d5*d5 + c3*c4*d2*d4*c5*c5*d1*d1 + c3*c4*d3*d5*c2*c2*d1*d1 + c3*c4*d4*d5*c1*c1*d2*d2
    + c3*c5*d1*d3*c2*c2*d4*d4 + c3*c5*d1*d5*c4*c4*d2*d2 + c3*c5*d2*d3*c4*c4*d1*d1 + c3*c5*d2*d5*c1*c1*d4*d4 + c3*c5*d3*d4*c1*c1*d2*d2 + c3*c5*d4*d5*c2*c2*d1*d1
    + c4*c5*d1*d4*c3*c3*d2*d2 + c4*c5*d1*d5*c2*c2*d3*d3 + c4*c5*d2*d4*c1*c1*d3*d3 + c4*c5*d2*d5*c3*c3*d1*d1 + c4*c5*d3*d4*c2*c2*d1*d1 + c4*c5*d3*d5*c1*c1*d2*d2
    - c1*c2*d1*d3*c4*c4*d5*d5 - c1*c2*d1*d4*c5*c5*d3*d3 - c1*c2*d1*d5*c3*c3*d4*d4 - c1*c2*d2*d3*c5*c5*d4*d4 - c1*c2*d2*d4*c3*c3*d5*d5 - c1*c2*d2*d5*c4*c4*d3*d3
    - c1*c3*d1*d2*c5*c5*d4*d4 - c1*c3*d1*d4*c2*c2*d5*d5 - c1*c3*d1*d5*c4*c4*d2*d2 - c1*c3*d2*d3*c4*c4*d5*d5 - c1*c3*d3*d4*c5*c5*d2*d2 - c1*c3*d3*d5*c2*c2*d4*d4
    - c1*c4*d1*d2*c3*c3*d5*d5 - c1*c4*d1*d3*c5*c5*d2*d2 - c1*c4*d1*d5*c2*c2*d3*d3 - c1*c4*d2*d4*c5*c5*d3*d3 - c1*c4*d3*d4*c2*c2*d5*d5 - c1*c4*d4*d5*c3*c3*d2*d2
    - c1*c5*d1*d2*c4*c4*d3*d3 - c1*c5*d1*d3*c2*c2*d4*d4 - c1*c5*d1*d4*c3*c3*d2*d2 - c1*c5*d2*d5*c3*c3*d4*d4 - c1*c5*d3*d5*c4*c4*d2*d2 - c1*c5*d4*d5*c2*c2*d3*d3
    - c2*c3*d1*d2*c4*c4*d5*d5 - c2*c3*d1*d3*c5*c5*d4*d4 - c2*c3*d2*d4*c5*c5*d1*d1 - c2*c3*d2*d5*c1*c1*d4*d4 - c2*c3*d3*d4*c1*c1*d5*d5 - c2*c3*d3*d5*c4*c4*d1*d1
    - c2*c4*d1*d2*c5*c5*d3*d3 - c2*c4*d1*d4*c3*c3*d5*d5 - c2*c4*d2*d3*c1*c1*d5*d5 - c2*c4*d2*d5*c3*c3*d1*d1 - c2*c4*d3*d4*c5*c5*d1*d1 - c2*c4*d4*d5*c1*c1*d3*d3
    - c2*c5*d1*d2*c3*c3*d4*d4 - c2*c5*d1*d5*c4*c4*d3*d3 - c2*c5*d2*d3*c4*c4*d1*d1 - c2*c5*d2*d4*c1*c1*d3*d3 - c2*c5*d3*d5*c1*c1*d4*d4 - c2*c5*d4*d5*c3*c3*d1*d1
    - c3*c4*d1*d3*c2*c2*d5*d5 - c3*c4*d1*d4*c5*c5*d2*d2 - c3*c4*d2*d3*c5*c5*d1*d1 - c3*c4*d2*d4*c1*c1*d5*d5 - c3*c4*d3*d5*c1*c1*d2*d2 - c3*c4*d4*d5*c2*c2*d1*d1
    - c3*c5*d1*d3*c4*c4*d2*d2 - c3*c5*d1*d5*c2*c2*d4*d4 - c3*c5*d2*d3*c1*c1*d4*d4 - c3*c5*d2*d5*c4*c4*d1*d1 - c3*c5*d3*d4*c2*c2*d1*d1 - c3*c5*d4*d5*c1*c1*d2*d2
    - c4*c5*d1*d4*c2*c2*d3*d3 - c4*c5*d1*d5*c3*c3*d2*d2 - c4*c5*d2*d4*c3*c3*d1*d1 - c4*c5*d2*d5*c1*c1*d3*d3 - c4*c5*d3*d4*c1*c1*d2*d2 - c4*c5*d3*d5*c2*c2*d1*d1

lemma WW_swap (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) : WW d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 = WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold WW; ring

lemma sub_of_cross {X₁ N₁ X₂ N₂ R : K} (h₁ : N₁ ≠ 0) (h₂ : N₂ ≠ 0) (h : X₁ * N₂ - N₁ * X₂ = R) :
    X₁ / N₁ - X₂ / N₂ = R * N₁⁻¹ * N₂⁻¹ := by
  rw [div_sub_div _ _ h₁ h₂, h, div_eq_mul_inv, mul_inv]; ring

lemma cross54 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) :
    XN c1 d1 c2 d2 c3 d3 c4 d4 * NN c1 d1 c2 d2 c3 d3 c5 d5 - NN c1 d1 c2 d2 c3 d3 c4 d4 * XN c1 d1 c2 d2 c3 d3 c5 d5 =
      d1 * d2 * d3 * LL c1 d1 c2 d2 c3 d3 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold XN NN LL WW; ring

lemma cross32 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) :
    XN c1 d1 c2 d2 c4 d4 c5 d5 * NN c1 d1 c3 d3 c4 d4 c5 d5 - NN c1 d1 c2 d2 c4 d4 c5 d5 * XN c1 d1 c3 d3 c4 d4 c5 d5 =
      d1 * d4 * d5 * LL c1 d1 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold XN NN LL WW; ring

lemma cross31 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) :
    XN c1 d1 c2 d2 c4 d4 c5 d5 * NN c2 d2 c3 d3 c4 d4 c5 d5 - NN c1 d1 c2 d2 c4 d4 c5 d5 * XN c2 d2 c3 d3 c4 d4 c5 d5 =
      d2 * d4 * d5 * LL c2 d2 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold XN NN LL WW; ring

lemma cross53 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) :
    XN c1 d1 c2 d2 c3 d3 c4 d4 * NN c1 d1 c2 d2 c4 d4 c5 d5 - NN c1 d1 c2 d2 c3 d3 c4 d4 * XN c1 d1 c2 d2 c4 d4 c5 d5 =
      d1 * d2 * d4 * LL c1 d1 c2 d2 c4 d4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold XN NN LL WW; ring

lemma cross42 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) :
    XN c1 d1 c2 d2 c3 d3 c5 d5 * NN c1 d1 c3 d3 c4 d4 c5 d5 - NN c1 d1 c2 d2 c3 d3 c5 d5 * XN c1 d1 c3 d3 c4 d4 c5 d5 =
      d1 * d3 * d5 * LL c1 d1 c3 d3 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold XN NN LL WW; ring

lemma cross41 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) :
    XN c1 d1 c2 d2 c3 d3 c5 d5 * NN c2 d2 c3 d3 c4 d4 c5 d5 - NN c1 d1 c2 d2 c3 d3 c5 d5 * XN c2 d2 c3 d3 c4 d4 c5 d5 =
      d2 * d3 * d5 * LL c2 d2 c3 d3 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold XN NN LL WW; ring

lemma cross43 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) :
    XN c1 d1 c2 d2 c3 d3 c5 d5 * NN c1 d1 c2 d2 c4 d4 c5 d5 - NN c1 d1 c2 d2 c3 d3 c5 d5 * XN c1 d1 c2 d2 c4 d4 c5 d5 =
      d1 * d2 * d5 * LL c1 d1 c2 d2 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold XN NN LL WW; ring

/-- `P₅, P₄, P₃, P_2` are concyclic (cross-ratio form). -/
lemma TT_five_2 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K)
    (h5 : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) (h4 : NN c1 d1 c2 d2 c3 d3 c5 d5 ≠ 0) (h3 : NN c1 d1 c2 d2 c4 d4 c5 d5 ≠ 0) (h2 : NN c1 d1 c3 d3 c4 d4 c5 d5 ≠ 0) (h5' : NN d1 c1 d2 c2 d3 c3 d4 c4 ≠ 0) (h4' : NN d1 c1 d2 c2 d3 c3 d5 c5 ≠ 0) (h3' : NN d1 c1 d2 c2 d4 c4 d5 c5 ≠ 0) (h2' : NN d1 c1 d3 c3 d4 c4 d5 c5 ≠ 0) :
    TT (XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4) (XN d1 c1 d2 c2 d3 c3 d4 c4 / NN d1 c1 d2 c2 d3 c3 d4 c4) (XN c1 d1 c2 d2 c3 d3 c5 d5 / NN c1 d1 c2 d2 c3 d3 c5 d5) (XN d1 c1 d2 c2 d3 c3 d5 c5 / NN d1 c1 d2 c2 d3 c3 d5 c5) (XN c1 d1 c2 d2 c4 d4 c5 d5 / NN c1 d1 c2 d2 c4 d4 c5 d5) (XN d1 c1 d2 c2 d4 c4 d5 c5 / NN d1 c1 d2 c2 d4 c4 d5 c5) (XN c1 d1 c3 d3 c4 d4 c5 d5 / NN c1 d1 c3 d3 c4 d4 c5 d5) (XN d1 c1 d3 c3 d4 c4 d5 c5 / NN d1 c1 d3 c3 d4 c4 d5 c5) = 0 := by
  unfold TT
  rw [sub_of_cross h5 h4 (cross54 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h3 h2 (cross32 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h5 h3 (cross53 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h4 h2 (cross42 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h5' h4' (cross54 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h3' h2' (cross32 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h5' h3' (cross53 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h4' h2' (cross42 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5)]
  rw [LL_swap c1 d1 c2 d2 c3 d3, LL_swap c1 d1 c2 d2 c4 d4, LL_swap c1 d1 c3 d3 c5 d5, LL_swap c1 d1 c4 d4 c5 d5, WW_swap c1 d1 c2 d2 c3 d3 c4 d4 c5 d5]
  ring

/-- `P₅, P₄, P₃, P_1` are concyclic (cross-ratio form). -/
lemma TT_five_1 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K)
    (h5 : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) (h4 : NN c1 d1 c2 d2 c3 d3 c5 d5 ≠ 0) (h3 : NN c1 d1 c2 d2 c4 d4 c5 d5 ≠ 0) (h1 : NN c2 d2 c3 d3 c4 d4 c5 d5 ≠ 0) (h5' : NN d1 c1 d2 c2 d3 c3 d4 c4 ≠ 0) (h4' : NN d1 c1 d2 c2 d3 c3 d5 c5 ≠ 0) (h3' : NN d1 c1 d2 c2 d4 c4 d5 c5 ≠ 0) (h1' : NN d2 c2 d3 c3 d4 c4 d5 c5 ≠ 0) :
    TT (XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4) (XN d1 c1 d2 c2 d3 c3 d4 c4 / NN d1 c1 d2 c2 d3 c3 d4 c4) (XN c1 d1 c2 d2 c3 d3 c5 d5 / NN c1 d1 c2 d2 c3 d3 c5 d5) (XN d1 c1 d2 c2 d3 c3 d5 c5 / NN d1 c1 d2 c2 d3 c3 d5 c5) (XN c1 d1 c2 d2 c4 d4 c5 d5 / NN c1 d1 c2 d2 c4 d4 c5 d5) (XN d1 c1 d2 c2 d4 c4 d5 c5 / NN d1 c1 d2 c2 d4 c4 d5 c5) (XN c2 d2 c3 d3 c4 d4 c5 d5 / NN c2 d2 c3 d3 c4 d4 c5 d5) (XN d2 c2 d3 c3 d4 c4 d5 c5 / NN d2 c2 d3 c3 d4 c4 d5 c5) = 0 := by
  unfold TT
  rw [sub_of_cross h5 h4 (cross54 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h3 h1 (cross31 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h5 h3 (cross53 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h4 h1 (cross41 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h5' h4' (cross54 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h3' h1' (cross31 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h5' h3' (cross53 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h4' h1' (cross41 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5)]
  rw [LL_swap c1 d1 c2 d2 c3 d3, LL_swap c1 d1 c2 d2 c4 d4, LL_swap c2 d2 c3 d3 c5 d5, LL_swap c2 d2 c4 d4 c5 d5, WW_swap c1 d1 c2 d2 c3 d3 c4 d4 c5 d5]
  ring

/-- If `A, B, C` are collinear and distinct and `T(A, B, C, Z) = 0`, then `Z` is on their line
(polynomial identity behind it). -/
lemma TT_den3 (A a B b C c Z z : K) :
    TT A a B b C c Z z - (A - B) * (a - c) * den3 B b C c Z z = (B - Z) * (z - c) * den3 A a B b C c := by
  unfold TT den3; ring

/-- Denominator of the common point of the n = 6 theorem: the 6 × 6 determinant with rows
`(dᵢ², dᵢ³, cᵢdᵢ, cᵢdᵢ², cᵢ²dᵢ, cᵢ²)`, written as its Laplace expansion along the last column. -/
def ZD (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : K :=
  c1^2 * d2 * d3 * d4 * d5 * d6 * WW c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - c2^2 * d1 * d3 * d4 * d5 * d6 * WW c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 + c3^2 * d1 * d2 * d4 * d5 * d6 * WW c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 - c4^2 * d1 * d2 * d3 * d5 * d6 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 + c5^2 * d1 * d2 * d3 * d4 * d6 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 - c6^2 * d1 * d2 * d3 * d4 * d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5

/-- Numerator of the common point (last column `cᵢ³`). -/
def ZN (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : K :=
  c1^3 * d2 * d3 * d4 * d5 * d6 * WW c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - c2^3 * d1 * d3 * d4 * d5 * d6 * WW c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 + c3^3 * d1 * d2 * d4 * d5 * d6 * WW c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 - c4^3 * d1 * d2 * d3 * d5 * d6 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 + c5^3 * d1 * d2 * d3 * d4 * d6 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 - c6^3 * d1 * d2 * d3 * d4 * d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5

def lam1 (c1 d1 c2 d2 c3 d3 c4 d4 : K) : K :=
    c1*d2*c4*c4*d3*d3 + c1*d3*c2*c2*d4*d4 + c1*d4*c3*c3*d2*d2 + c2*d1*c3*c3*d4*d4 + c2*d3*c4*c4*d1*d1 + c2*d4*c1*c1*d3*d3
    + c3*d1*c4*c4*d2*d2 + c3*d2*c1*c1*d4*d4 + c3*d4*c2*c2*d1*d1 + c4*d1*c2*c2*d3*d3 + c4*d2*c3*c3*d1*d1 + c4*d3*c1*c1*d2*d2
    - c1*d2*c3*c3*d4*d4 - c1*d3*c4*c4*d2*d2 - c1*d4*c2*c2*d3*d3 - c2*d1*c4*c4*d3*d3 - c2*d3*c1*c1*d4*d4 - c2*d4*c3*c3*d1*d1
    - c3*d1*c2*c2*d4*d4 - c3*d2*c4*c4*d1*d1 - c3*d4*c1*c1*d2*d2 - c4*d1*c3*c3*d2*d2 - c4*d2*c1*c1*d3*d3 - c4*d3*c2*c2*d1*d1

def lam2 (c1 d1 c2 d2 c3 d3 c4 d4 : K) : K :=
    c1*c2*d1*d4*c3*c3 + c1*c2*d2*d3*c4*c4 + c1*c3*d1*d2*c4*c4 + c1*c3*d3*d4*c2*c2 + c1*c4*d1*d3*c2*c2 + c1*c4*d2*d4*c3*c3
    + c2*c3*d1*d3*c4*c4 + c2*c3*d2*d4*c1*c1 + c2*c4*d1*d2*c3*c3 + c2*c4*d3*d4*c1*c1 + c3*c4*d1*d4*c2*c2 + c3*c4*d2*d3*c1*c1
    - c1*c2*d1*d3*c4*c4 - c1*c2*d2*d4*c3*c3 - c1*c3*d1*d4*c2*c2 - c1*c3*d2*d3*c4*c4 - c1*c4*d1*d2*c3*c3 - c1*c4*d3*d4*c2*c2
    - c2*c3*d1*d2*c4*c4 - c2*c3*d3*d4*c1*c1 - c2*c4*d1*d4*c3*c3 - c2*c4*d2*d3*c1*c1 - c3*c4*d1*d3*c2*c2 - c3*c4*d2*d4*c1*c1

def lam4 (c1 d1 c2 d2 c3 d3 c4 d4 : K) : K :=
    c1*c2*d1*c4*c4*d3*d3 + c1*c2*d2*c3*c3*d4*d4 + c1*c3*d1*c2*c2*d4*d4 + c1*c3*d3*c4*c4*d2*d2 + c1*c4*d1*c3*c3*d2*d2 + c1*c4*d4*c2*c2*d3*d3
    + c2*c3*d2*c4*c4*d1*d1 + c2*c3*d3*c1*c1*d4*d4 + c2*c4*d2*c1*c1*d3*d3 + c2*c4*d4*c3*c3*d1*d1 + c3*c4*d3*c2*c2*d1*d1 + c3*c4*d4*c1*c1*d2*d2
    - c1*c2*d1*c3*c3*d4*d4 - c1*c2*d2*c4*c4*d3*d3 - c1*c3*d1*c4*c4*d2*d2 - c1*c3*d3*c2*c2*d4*d4 - c1*c4*d1*c2*c2*d3*d3 - c1*c4*d4*c3*c3*d2*d2
    - c2*c3*d2*c1*c1*d4*d4 - c2*c3*d3*c4*c4*d1*d1 - c2*c4*d2*c3*c3*d1*d1 - c2*c4*d4*c1*c1*d3*d3 - c3*c4*d3*c1*c1*d2*d2 - c3*c4*d4*c2*c2*d1*d1

/-- `-NN, lam1, lam2, XN, lam4` are the cofactors of the 4 × 5 matrix with rows
`(cᵢ², cᵢdᵢ, dᵢ², cᵢ, dᵢ)`. -/
lemma cof_WW (c1 d1 c2 d2 c3 d3 c4 d4 x y : K) :
    -NN c1 d1 c2 d2 c3 d3 c4 d4 * x^2 + lam1 c1 d1 c2 d2 c3 d3 c4 d4 * (x*y) + lam2 c1 d1 c2 d2 c3 d3 c4 d4 * y^2 + XN c1 d1 c2 d2 c3 d3 c4 d4 * x + lam4 c1 d1 c2 d2 c3 d3 c4 d4 * y =
      WW c1 d1 c2 d2 c3 d3 c4 d4 x y := by
  unfold NN XN lam1 lam2 lam4 WW; ring

lemma WW_rep1 (c1 d1 c2 d2 c3 d3 c4 d4 : K) : WW c1 d1 c2 d2 c3 d3 c4 d4 c1 d1 = 0 := by
  unfold WW; ring

lemma WW_rep2 (c1 d1 c2 d2 c3 d3 c4 d4 : K) : WW c1 d1 c2 d2 c3 d3 c4 d4 c2 d2 = 0 := by
  unfold WW; ring

lemma WW_rep3 (c1 d1 c2 d2 c3 d3 c4 d4 : K) : WW c1 d1 c2 d2 c3 d3 c4 d4 c3 d3 = 0 := by
  unfold WW; ring

lemma WW_rep4 (c1 d1 c2 d2 c3 d3 c4 d4 : K) : WW c1 d1 c2 d2 c3 d3 c4 d4 c4 d4 = 0 := by
  unfold WW; ring

lemma lap_c (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) :
    c1 * WW c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - c2 * WW c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 + c3 * WW c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 - c4 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 + c5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 - c6 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 = 0 := by
  unfold WW; ring

lemma lap_cd (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) :
    (c1*d1) * WW c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - (c2*d2) * WW c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 + (c3*d3) * WW c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 - (c4*d4) * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 + (c5*d5) * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 - (c6*d6) * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 = 0 := by
  unfold WW; ring

lemma lap_cc (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) :
    c1^2 * WW c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - c2^2 * WW c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 + c3^2 * WW c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 - c4^2 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 + c5^2 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 - c6^2 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 = 0 := by
  unfold WW; ring

/-- The master identity: `P_{1234} - Q` factors (`Q = ZN / ZD`). -/
lemma master (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) :
    XN c1 d1 c2 d2 c3 d3 c4 d4 * ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - NN c1 d1 c2 d2 c3 d3 c4 d4 * ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 =
      d1 * d2 * d3 * d4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 * ee c5 d5 c6 d6 := by
  have q1 := (cof_WW c1 d1 c2 d2 c3 d3 c4 d4 c1 d1).trans (WW_rep1 c1 d1 c2 d2 c3 d3 c4 d4)
  have q2 := (cof_WW c1 d1 c2 d2 c3 d3 c4 d4 c2 d2).trans (WW_rep2 c1 d1 c2 d2 c3 d3 c4 d4)
  have q3 := (cof_WW c1 d1 c2 d2 c3 d3 c4 d4 c3 d3).trans (WW_rep3 c1 d1 c2 d2 c3 d3 c4 d4)
  have q4 := (cof_WW c1 d1 c2 d2 c3 d3 c4 d4 c4 d4).trans (WW_rep4 c1 d1 c2 d2 c3 d3 c4 d4)
  have q5 := cof_WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5
  have q6 := cof_WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6
  have r1 := lap_cc c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6
  have r2 := lap_cd c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6
  have r3 := lap_c c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6
  unfold ZD ZN ee
  linear_combination (1 : K) * WW c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 * (d2 * d3 * d4 * d5 * d6) * c1 * q1 + (-1 : K) * WW c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 * (d1 * d3 * d4 * d5 * d6) * c2 * q2 + (1 : K) * WW c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 * (d1 * d2 * d4 * d5 * d6) * c3 * q3 + (-1 : K) * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 * (d1 * d2 * d3 * d5 * d6) * c4 * q4 + (1 : K) * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 * (d1 * d2 * d3 * d4 * d6) * c5 * q5 + (-1 : K) * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * (d1 * d2 * d3 * d4 * d5) * c6 * q6
    - (d1*d2*d3*d4*d5*d6) * (lam1 c1 d1 c2 d2 c3 d3 c4 d4 * r1 + lam2 c1 d1 c2 d2 c3 d3 c4 d4 * r2 + lam4 c1 d1 c2 d2 c3 d3 c4 d4 * r3)

lemma ZD_p45 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZD c1 d1 c2 d2 c3 d3 c5 d5 c4 d4 c6 d6 = -ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZD WW; ring

lemma ZN_p45 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZN c1 d1 c2 d2 c3 d3 c5 d5 c4 d4 c6 d6 = -ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZN WW; ring

lemma ZD_p345 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZD c1 d1 c2 d2 c4 d4 c5 d5 c3 d3 c6 d6 = ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZD WW; ring

lemma ZN_p345 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZN c1 d1 c2 d2 c4 d4 c5 d5 c3 d3 c6 d6 = ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZN WW; ring

lemma ZD_o1 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZD c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 c1 d1 = -ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZD WW; ring

lemma ZN_o1 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZN c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 c1 d1 = -ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZN WW; ring

lemma ZD_o2 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZD c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 c2 d2 = ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZD WW; ring

lemma ZN_o2 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZN c1 d1 c3 d3 c4 d4 c5 d5 c6 d6 c2 d2 = ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZN WW; ring

lemma ZD_o3 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZD c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 c3 d3 = -ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZD WW; ring

lemma ZN_o3 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZN c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 c3 d3 = -ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZN WW; ring

lemma ZD_o4 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZD c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 c4 d4 = ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZD WW; ring

lemma ZN_o4 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZN c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 c4 d4 = ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZN WW; ring

lemma ZD_o5 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZD c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 c5 d5 = -ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZD WW; ring

lemma ZN_o5 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) : ZN c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 c5 d5 = -ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 := by
  unfold ZN WW; ring

lemma WW_p45 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) : WW c1 d1 c2 d2 c3 d3 c5 d5 c4 d4 = -WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold WW; ring

lemma WW_p345 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K) : WW c1 d1 c2 d2 c4 d4 c5 d5 c3 d3 = WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 := by
  unfold WW; ring

lemma master1235 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) :
    XN c1 d1 c2 d2 c3 d3 c5 d5 * ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - NN c1 d1 c2 d2 c3 d3 c5 d5 * ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 =
      d1 * d2 * d3 * d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 * ee c4 d4 c6 d6 := by
  have h := master c1 d1 c2 d2 c3 d3 c5 d5 c4 d4 c6 d6
  rw [ZD_p45, ZN_p45, WW_p45] at h
  linear_combination -h

lemma master1245 (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K) :
    XN c1 d1 c2 d2 c4 d4 c5 d5 * ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 - NN c1 d1 c2 d2 c4 d4 c5 d5 * ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 =
      d1 * d2 * d4 * d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c4 d4 c5 d5 c6 d6 * ee c3 d3 c6 d6 := by
  have h := master c1 d1 c2 d2 c4 d4 c5 d5 c3 d3 c6 d6
  rw [ZD_p345, ZN_p345, WW_p345] at h
  exact h

/-- The common point `Q = ZN / ZD` is concyclic with `P₅, P₄, P₃`. -/
lemma TT_Q (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K)
    (h5 : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) (h4 : NN c1 d1 c2 d2 c3 d3 c5 d5 ≠ 0) (h3 : NN c1 d1 c2 d2 c4 d4 c5 d5 ≠ 0)
    (h5' : NN d1 c1 d2 c2 d3 c3 d4 c4 ≠ 0) (h4' : NN d1 c1 d2 c2 d3 c3 d5 c5 ≠ 0) (h3' : NN d1 c1 d2 c2 d4 c4 d5 c5 ≠ 0)
    (hZ : ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 ≠ 0) (hZ' : ZD d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6 ≠ 0) :
    TT (XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4) (XN d1 c1 d2 c2 d3 c3 d4 c4 / NN d1 c1 d2 c2 d3 c3 d4 c4) (XN c1 d1 c2 d2 c3 d3 c5 d5 / NN c1 d1 c2 d2 c3 d3 c5 d5) (XN d1 c1 d2 c2 d3 c3 d5 c5 / NN d1 c1 d2 c2 d3 c3 d5 c5) (XN c1 d1 c2 d2 c4 d4 c5 d5 / NN c1 d1 c2 d2 c4 d4 c5 d5) (XN d1 c1 d2 c2 d4 c4 d5 c5 / NN d1 c1 d2 c2 d4 c4 d5 c5)
      (ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 / ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6) (ZN d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6 / ZD d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6) = 0 := by
  unfold TT
  rw [sub_of_cross h5 h4 (cross54 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5), sub_of_cross h5 h3 (cross53 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5),
    sub_of_cross h3 hZ (master1245 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6), sub_of_cross h4 hZ (master1235 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6),
    sub_of_cross h5' h4' (cross54 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h5' h3' (cross53 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5),
    sub_of_cross h3' hZ' (master1245 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6), sub_of_cross h4' hZ' (master1235 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6)]
  rw [LL_swap c1 d1 c2 d2 c3 d3, LL_swap c1 d1 c2 d2 c4 d4, WW_swap c1 d1 c2 d2 c3 d3 c4 d4 c5 d5,
    WW_swap c1 d1 c2 d2 c4 d4 c5 d5 c6 d6, WW_swap c1 d1 c2 d2 c3 d3 c5 d5 c6 d6, ee_swap c3 d3 c6 d6, ee_swap c4 d4 c6 d6]
  ring

lemma den3_alt (A a B b C c : K) : den3 A a B b C c = (a - c) * (B - C) - (b - c) * (A - C) := by
  unfold den3; ring

lemma den3_mul (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 : K)
    (h5 : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) (h4 : NN c1 d1 c2 d2 c3 d3 c5 d5 ≠ 0) (h3 : NN c1 d1 c2 d2 c4 d4 c5 d5 ≠ 0)
    (h5' : NN d1 c1 d2 c2 d3 c3 d4 c4 ≠ 0) (h4' : NN d1 c1 d2 c2 d3 c3 d5 c5 ≠ 0) (h3' : NN d1 c1 d2 c2 d4 c4 d5 c5 ≠ 0) :
    den3 (XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4) (XN d1 c1 d2 c2 d3 c3 d4 c4 / NN d1 c1 d2 c2 d3 c3 d4 c4) (XN c1 d1 c2 d2 c3 d3 c5 d5 / NN c1 d1 c2 d2 c3 d3 c5 d5) (XN d1 c1 d2 c2 d3 c3 d5 c5 / NN d1 c1 d2 c2 d3 c3 d5 c5) (XN c1 d1 c2 d2 c4 d4 c5 d5 / NN c1 d1 c2 d2 c4 d4 c5 d5) (XN d1 c1 d2 c2 d4 c4 d5 c5 / NN d1 c1 d2 c2 d4 c4 d5 c5) *
        (NN c1 d1 c2 d2 c3 d3 c4 d4 * NN c1 d1 c2 d2 c3 d3 c5 d5 * NN c1 d1 c2 d2 c4 d4 c5 d5 * NN d1 c1 d2 c2 d3 c3 d4 c4 * NN d1 c1 d2 c2 d3 c3 d5 c5 * NN d1 c1 d2 c2 d4 c4 d5 c5) =
      (c1 * c2 * c4 * LL d1 c1 d2 c2 d4 c4 * WW d1 c1 d2 c2 d3 c3 d4 c4 d5 c5) * (d1 * d2 * d5 * LL c1 d1 c2 d2 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5)
          * NN d1 c1 d2 c2 d3 c3 d5 c5 * NN c1 d1 c2 d2 c3 d3 c4 d4
        - (c1 * c2 * c5 * LL d1 c1 d2 c2 d5 c5 * WW d1 c1 d2 c2 d3 c3 d4 c4 d5 c5) * (d1 * d2 * d4 * LL c1 d1 c2 d2 c4 d4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5)
          * NN d1 c1 d2 c2 d3 c3 d4 c4 * NN c1 d1 c2 d2 c3 d3 c5 d5 := by
  rw [den3_alt, sub_of_cross h5' h3' (cross53 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h4 h3 (cross43 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5),
    sub_of_cross h4' h3' (cross43 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5), sub_of_cross h5 h3 (cross53 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5)]
  field_simp

/-- If `ZD = 0` then `P₅, P₄, P₃` are collinear (or `ZN = 0`). -/
lemma den3_of_ZD (c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 : K)
    (h5 : NN c1 d1 c2 d2 c3 d3 c4 d4 ≠ 0) (h4 : NN c1 d1 c2 d2 c3 d3 c5 d5 ≠ 0) (h3 : NN c1 d1 c2 d2 c4 d4 c5 d5 ≠ 0)
    (h5' : NN d1 c1 d2 c2 d3 c3 d4 c4 ≠ 0) (h4' : NN d1 c1 d2 c2 d3 c3 d5 c5 ≠ 0) (h3' : NN d1 c1 d2 c2 d4 c4 d5 c5 ≠ 0)
    (hZ : ZD c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 = 0) (hZ' : ZD d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6 = 0) :
    den3 (XN c1 d1 c2 d2 c3 d3 c4 d4 / NN c1 d1 c2 d2 c3 d3 c4 d4) (XN d1 c1 d2 c2 d3 c3 d4 c4 / NN d1 c1 d2 c2 d3 c3 d4 c4) (XN c1 d1 c2 d2 c3 d3 c5 d5 / NN c1 d1 c2 d2 c3 d3 c5 d5) (XN d1 c1 d2 c2 d3 c3 d5 c5 / NN d1 c1 d2 c2 d3 c3 d5 c5) (XN c1 d1 c2 d2 c4 d4 c5 d5 / NN c1 d1 c2 d2 c4 d4 c5 d5) (XN d1 c1 d2 c2 d4 c4 d5 c5 / NN d1 c1 d2 c2 d4 c4 d5 c5) *
        (NN c1 d1 c2 d2 c3 d3 c4 d4 * NN c1 d1 c2 d2 c3 d3 c5 d5 * NN c1 d1 c2 d2 c4 d4 c5 d5 * NN d1 c1 d2 c2 d3 c3 d4 c4 * NN d1 c1 d2 c2 d3 c3 d5 c5 * NN d1 c1 d2 c2 d4 c4 d5 c5) *
        (ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 * ZN d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6) = 0 := by
  rw [den3_mul c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 h5 h4 h3 h5' h4' h3']
  have m5 := master c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6
  have m4 := master1235 c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6
  have m5' := master d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6
  have m4' := master1235 d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6
  rw [WW_swap c1 d1 c2 d2 c3 d3 c4 d4 c5 d5, WW_swap c1 d1 c2 d2 c3 d3 c4 d4 c6 d6, ee_swap c5 d5 c6 d6] at m5'
  rw [WW_swap c1 d1 c2 d2 c3 d3 c4 d4 c5 d5, WW_swap c1 d1 c2 d2 c3 d3 c5 d5 c6 d6, ee_swap c4 d4 c6 d6] at m4'
  rw [LL_swap c1 d1 c2 d2 c4 d4, LL_swap c1 d1 c2 d2 c5 d5, WW_swap c1 d1 c2 d2 c3 d3 c4 d4 c5 d5]
  have E5 : NN c1 d1 c2 d2 c3 d3 c4 d4 * ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 = -(d1 * d2 * d3 * d4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 * ee c5 d5 c6 d6) := by
    linear_combination XN c1 d1 c2 d2 c3 d3 c4 d4 * hZ - m5
  have E4 : NN c1 d1 c2 d2 c3 d3 c5 d5 * ZN c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 c6 d6 = -(d1 * d2 * d3 * d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 * ee c4 d4 c6 d6) := by
    linear_combination XN c1 d1 c2 d2 c3 d3 c5 d5 * hZ - m4
  have E5' : NN d1 c1 d2 c2 d3 c3 d4 c4 * ZN d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6 = -(c1 * c2 * c3 * c4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 * -ee c5 d5 c6 d6) := by
    linear_combination XN d1 c1 d2 c2 d3 c3 d4 c4 * hZ' - m5'
  have E4' : NN d1 c1 d2 c2 d3 c3 d5 c5 * ZN d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6 = -(c1 * c2 * c3 * c5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 * -ee c4 d4 c6 d6) := by
    linear_combination XN d1 c1 d2 c2 d3 c3 d5 c5 * hZ' - m4'
  linear_combination
    ((c1 * c2 * c4 * -LL c1 d1 c2 d2 c4 d4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5) * (d1 * d2 * d5 * LL c1 d1 c2 d2 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5)) *
      (NN d1 c1 d2 c2 d3 c3 d5 c5 * ZN d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6 * E5 + (-(d1 * d2 * d3 * d4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c6 d6 * ee c5 d5 c6 d6)) * E4')
    - ((c1 * c2 * c5 * -LL c1 d1 c2 d2 c5 d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5) * (d1 * d2 * d4 * LL c1 d1 c2 d2 c4 d4 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5)) *
      (NN d1 c1 d2 c2 d3 c3 d4 c4 * ZN d1 c1 d2 c2 d3 c3 d4 c4 d5 c5 d6 c6 * E4 + (-(d1 * d2 * d3 * d5 * WW c1 d1 c2 d2 c3 d3 c4 d4 c5 d5 * WW c1 d1 c2 d2 c3 d3 c5 d5 c6 d6 * ee c4 d4 c6 d6)) * E5')

lemma ne_of_cross {X₁ N₁ X₂ N₂ R : K} (h₁ : N₁ ≠ 0) (h₂ : N₂ ≠ 0) (h : X₁ * N₂ - N₁ * X₂ = R)
    (hR : R ≠ 0) : X₁ / N₁ ≠ X₂ / N₂ := by
  intro he
  have := sub_of_cross h₁ h₂ h
  rw [he, sub_self] at this
  exact mul_ne_zero (mul_ne_zero hR (inv_ne_zero h₁)) (inv_ne_zero h₂) this.symm

lemma eq_of_cross {X₁ N₁ X₂ N₂ R : K} (h₁ : N₁ ≠ 0) (h₂ : N₂ ≠ 0) (h : X₁ * N₂ - N₁ * X₂ = R)
    (hR : R = 0) : X₁ / N₁ = X₂ / N₂ := by
  have := sub_of_cross h₁ h₂ h
  rw [hR, zero_mul, zero_mul] at this
  exact sub_eq_zero.1 this

end Generic

/-! ### Back in `ℂ` -/

lemma conj_ne_zero_right {c₁ c₂ : ℂ} (h : secondInter c₁ c₂ ≠ 0) : conj c₂ ≠ 0 := by
  obtain ⟨-, -, e⟩ := secondInter_ne_zero_iff' h
  intro h0; apply e; unfold ee; rw [h0, (map_eq_zero _).1 h0]; ring

lemma conj_ne_zero_left {c₁ c₂ : ℂ} (h : secondInter c₁ c₂ ≠ 0) : conj c₁ ≠ 0 :=
  conj_ne_zero_right (by rwa [secondInter_symm])

/-- Non-collinearity of the second intersection points of a triple gives `LL ≠ 0` and `DD ≠ 0`. -/
lemma triple_LL_DD {c₁ c₂ c₃ : ℂ} (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0)
    (h23 : secondInter c₂ c₃ ≠ 0)
    (hnc : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ)) :
    LL c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) ≠ 0 ∧ DD c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) ≠ 0 := by
  obtain ⟨d12, g12, -⟩ := secondInter_ne_zero_iff' h12
  obtain ⟨d13, g13, -⟩ := secondInter_ne_zero_iff' h13
  obtain ⟨d23, g23, -⟩ := secondInter_ne_zero_iff' h23
  have hden := den3_ne_zero hnc
  unfold secondInter at hden
  simp only [conj_sec, Complex.conj_conj] at hden
  rw [den3_sec _ _ _ _ _ _ d12 d13 d23 g12 g13 g23] at hden
  constructor
  · intro h0; apply hden; rw [h0]; ring
  · intro h0; apply hden; rw [h0]; ring

/-- The denominator of `cliffordPoint` (and of its conjugate) does not vanish. -/
lemma NN_ne_zero' {c₁ c₂ c₃ c₄ : ℂ}
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0)
    (hnc : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ)) :
    NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) ≠ 0 ∧
      NN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ ≠ 0 := by
  obtain ⟨-, -, e12⟩ := secondInter_ne_zero_iff' h12
  obtain ⟨-, -, e13⟩ := secondInter_ne_zero_iff' h13
  obtain ⟨d14, -, -⟩ := secondInter_ne_zero_iff' h14
  obtain ⟨-, -, e23⟩ := secondInter_ne_zero_iff' h23
  obtain ⟨d24, -, -⟩ := secondInter_ne_zero_iff' h24
  obtain ⟨d34, -, -⟩ := secondInter_ne_zero_iff' h34
  obtain ⟨hL, hD⟩ := triple_LL_DD h12 h13 h23 hnc
  have hc4 : conj c₄ ≠ 0 := conj_ne_zero_right h14
  have hN : NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) ≠ 0 := by
    intro h0
    have h0' : NN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ = 0 := by
      have := congrArg conj h0
      rw [conj_NN, map_zero] at this
      simpa only [Complex.conj_conj] using this
    have hR := resultant_NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄)
    rw [h0, h0', mul_zero, mul_zero, sub_zero] at hR
    exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero
      (mul_ne_zero (mul_ne_zero hc4 d14) d24) d34) e12) e13) e23) hL) hD) hR.symm
  refine ⟨hN, fun h0 => hN ?_⟩
  have := congrArg conj h0
  rw [conj_NN, map_zero] at this
  simpa only [Complex.conj_conj] using this

lemma conj_cliffordPoint (c₁ c₂ c₃ c₄ : ℂ) :
    conj (cliffordPoint c₁ c₂ c₃ c₄) =
      XN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ /
        NN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ := by
  unfold cliffordPoint
  rw [map_div₀, conj_XN, conj_NN]
  simp only [Complex.conj_conj]

/-- Collinear points have vanishing circumcentre denominator. -/
lemma den3_eq_zero_of_collinear {A B C : ℂ} (h : Collinear ℝ ({A, B, C} : Set ℂ)) :
    den3 A (conj A) B (conj B) C (conj C) = 0 := by
  rw [collinear_iff_of_mem (p₀ := A) (by simp)] at h
  obtain ⟨v, hv⟩ := h
  obtain ⟨r, hr⟩ := hv B (by simp)
  obtain ⟨s, hs⟩ := hv C (by simp)
  rw [vadd_eq_add, Complex.real_smul] at hr hs
  rw [hr, hs]
  simp only [map_add, map_mul, Complex.conj_ofReal]
  unfold den3; ring

lemma collinear_of_den3_eq_zero {A B C : ℂ} (h : den3 A (conj A) B (conj B) C (conj C) = 0) :
    Collinear ℝ ({A, B, C} : Set ℂ) := by
  by_contra h'; exact den3_ne_zero h' h

/-- If `A, B, C` are collinear with `A ≠ B`, `A ≠ C`, and `T(A, B, C, Z) = 0`, then `B, C, Z` are
collinear. -/
lemma collinear_of_TT {A B C Z : ℂ} (hAB : A ≠ B) (hAC : A ≠ C) (h : Collinear ℝ ({A, B, C} : Set ℂ))
    (hT : TT A (conj A) B (conj B) C (conj C) Z (conj Z) = 0) : Collinear ℝ ({B, C, Z} : Set ℂ) := by
  apply collinear_of_den3_eq_zero
  have e := TT_den3 A (conj A) B (conj B) C (conj C) Z (conj Z)
  rw [hT, den3_eq_zero_of_collinear h, mul_zero, zero_sub, neg_eq_zero] at e
  have h1 : A - B ≠ 0 := sub_ne_zero.2 hAB
  have h2 : conj A - conj C ≠ 0 := by
    rw [← map_sub]; exact (map_ne_zero _).2 (sub_ne_zero.2 hAC)
  exact (mul_eq_zero.1 e).resolve_left (mul_ne_zero h1 h2)

/-- The explicit point `cliffordPoint` is the common point of the four circles of `clifford_one`. -/
theorem cliffordPoint_mem_gams (c₁ c₂ c₃ c₄ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ)) :
    cliffordPoint c₁ c₂ c₃ c₄ ∈ gam c₁ c₂ c₃ ∧ cliffordPoint c₁ c₂ c₃ c₄ ∈ gam c₁ c₂ c₄ ∧
      cliffordPoint c₁ c₂ c₃ c₄ ∈ gam c₁ c₃ c₄ ∧ cliffordPoint c₁ c₂ c₃ c₄ ∈ gam c₂ c₃ c₄ := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact cliffordPoint_mem_gam c₁ c₂ c₃ c₄ h12 h13 h14 h23 h24 h34 n123
  · rw [← cliffordPoint_perm₁]
    exact cliffordPoint_mem_gam c₁ c₂ c₄ c₃ h12 h14 h13 h24 h23
      (by rwa [secondInter_symm]) n124
  · rw [← cliffordPoint_perm₂]
    exact cliffordPoint_mem_gam c₁ c₃ c₄ c₂ h13 h14 h12 h34 (by rwa [secondInter_symm])
      (by rwa [secondInter_symm]) n134
  · rw [← cliffordPoint_perm₃]
    exact cliffordPoint_mem_gam c₂ c₃ c₄ c₁ h23 h24 (by rwa [secondInter_symm]) h34
      (by rwa [secondInter_symm]) (by rwa [secondInter_symm]) n234

/-- **Clifford's second circle theorem (n = 5), explicit form.**  The five Clifford points
`P_k = cliffordPoint` (of the four circles other than circle `k`) are concyclic or collinear. -/
theorem clifford_two_explicit (c₁ c₂ c₃ c₄ c₅ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ)) :
    Cospherical ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₄} : Set ℂ) ∨
      Collinear ℝ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₄} : Set ℂ) := by
  obtain ⟨N5, N5'⟩ := NN_ne_zero' h12 h13 h14 h23 h24 h34 n123
  obtain ⟨N4, N4'⟩ := NN_ne_zero' h12 h13 h15 h23 h25 h35 n123
  obtain ⟨N3, N3'⟩ := NN_ne_zero' h12 h14 h15 h24 h25 h45 n124
  obtain ⟨N2, N2'⟩ := NN_ne_zero' h13 h14 h15 h34 h35 h45 n134
  obtain ⟨N1, N1'⟩ := NN_ne_zero' h23 h24 h25 h34 h35 h45 n234
  have d1 : conj c₁ ≠ 0 := conj_ne_zero_left h12
  have d2 : conj c₂ ≠ 0 := conj_ne_zero_right h12
  have d3 : conj c₃ ≠ 0 := conj_ne_zero_right h13
  have d4 : conj c₄ ≠ 0 := conj_ne_zero_right h14
  have d5 : conj c₅ ≠ 0 := conj_ne_zero_right h15
  have L123 := (triple_LL_DD h12 h13 h23 n123).1
  have L124 := (triple_LL_DD h12 h14 h24 n124).1
  have L125 := (triple_LL_DD h12 h15 h25 n125).1
  have T2 : TT (cliffordPoint c₁ c₂ c₃ c₄) (conj (cliffordPoint c₁ c₂ c₃ c₄)) (cliffordPoint c₁ c₂ c₃ c₅) (conj (cliffordPoint c₁ c₂ c₃ c₅))
      (cliffordPoint c₁ c₂ c₄ c₅) (conj (cliffordPoint c₁ c₂ c₄ c₅)) (cliffordPoint c₁ c₃ c₄ c₅) (conj (cliffordPoint c₁ c₃ c₄ c₅)) = 0 := by
    rw [conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint]
    exact TT_five_2 _ _ _ _ _ _ _ _ _ _ N5 N4 N3 N2 N5' N4' N3' N2'
  have T1 : TT (cliffordPoint c₁ c₂ c₃ c₄) (conj (cliffordPoint c₁ c₂ c₃ c₄)) (cliffordPoint c₁ c₂ c₃ c₅) (conj (cliffordPoint c₁ c₂ c₃ c₅))
      (cliffordPoint c₁ c₂ c₄ c₅) (conj (cliffordPoint c₁ c₂ c₄ c₅)) (cliffordPoint c₂ c₃ c₄ c₅) (conj (cliffordPoint c₂ c₃ c₄ c₅)) = 0 := by
    rw [conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint]
    exact TT_five_1 _ _ _ _ _ _ _ _ _ _ N5 N4 N3 N1 N5' N4' N3' N1'
  by_cases hW : WW c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) = 0
  · have e54 : cliffordPoint c₁ c₂ c₃ c₄ = cliffordPoint c₁ c₂ c₃ c₅ := eq_of_cross N5 N4 (cross54 ..) (by rw [hW, mul_zero])
    have e53 : cliffordPoint c₁ c₂ c₃ c₄ = cliffordPoint c₁ c₂ c₄ c₅ := eq_of_cross N5 N3 (cross53 ..) (by rw [hW, mul_zero])
    have e32 : cliffordPoint c₁ c₂ c₄ c₅ = cliffordPoint c₁ c₃ c₄ c₅ := eq_of_cross N3 N2 (cross32 ..) (by rw [hW, mul_zero])
    have e31 : cliffordPoint c₁ c₂ c₄ c₅ = cliffordPoint c₂ c₃ c₄ c₅ := eq_of_cross N3 N1 (cross31 ..) (by rw [hW, mul_zero])
    refine Or.inr ((collinear_singleton ℝ (cliffordPoint c₁ c₂ c₃ c₄)).subset ?_)
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    rcases hx with h | h | h | h | h <;> rw [h]
    · rw [← e31, e53]
    · rw [← e32, e53]
    · rw [e53]
    · rw [e54]
  have ne54 : cliffordPoint c₁ c₂ c₃ c₄ ≠ cliffordPoint c₁ c₂ c₃ c₅ := ne_of_cross N5 N4 (cross54 ..)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero d1 d2) d3) L123) hW)
  have ne53 : cliffordPoint c₁ c₂ c₃ c₄ ≠ cliffordPoint c₁ c₂ c₄ c₅ := ne_of_cross N5 N3 (cross53 ..)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero d1 d2) d4) L124) hW)
  have ne43 : cliffordPoint c₁ c₂ c₃ c₅ ≠ cliffordPoint c₁ c₂ c₄ c₅ := ne_of_cross N4 N3 (cross43 ..)
    (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero d1 d2) d5) L125) hW)
  by_cases hc : Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ)
  · right
    have k2 := collinear_of_TT ne54 ne53 hc T2
    have k1 := collinear_of_TT ne54 ne53 hc T1
    have m5 := hc.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) ne43 (p₃ := cliffordPoint c₁ c₂ c₃ c₄)
    have m2 := k2.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) ne43 (p₃ := cliffordPoint c₁ c₃ c₄ c₅)
    have m1 := k1.mem_affineSpan_of_mem_of_ne (by simp) (by simp) (by simp) ne43 (p₃ := cliffordPoint c₂ c₃ c₄ c₅)
    refine (collinear_insert_insert_insert_of_mem_affineSpan_pair m1 m2 m5).subset ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx ⊢
    tauto
  · left
    refine ⟨(circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅)).center,
      (circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅)).radius, ?_⟩
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact EuclideanGeometry.mem_sphere.1 (mem_circumcircle_of_TT hc T1)
    · exact EuclideanGeometry.mem_sphere.1 (mem_circumcircle_of_TT hc T2)
    · exact EuclideanGeometry.mem_sphere.1 (mem_circumcircle_right hc)
    · exact EuclideanGeometry.mem_sphere.1 (mem_circumcircle_middle hc)
    · exact EuclideanGeometry.mem_sphere.1 (mem_circumcircle_left _ _ _)

/-- **Clifford's second circle theorem (n = 5).**
Five circles through `M = 0` (centres `c₁, …, c₅`) in general position: no two are tangent at `M` or
coincide, and for every triple the three second intersection points are not collinear (so all the
circles `Γ_ijk = gam cᵢ cⱼ cₖ` are genuine circles).  For each `k`, the four circles `Γ` of the triples
avoiding `k` pass through a common point `P_k` (Clifford's first theorem), and the five points
`P₁, …, P₅` lie on one circle — or, in degenerate configurations, on one line. -/
theorem clifford_two (c₁ c₂ c₃ c₄ c₅ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ)) :
    ∃ P₁ P₂ P₃ P₄ P₅ : ℂ,
      (P₁ ∈ gam c₂ c₃ c₄ ∧ P₁ ∈ gam c₂ c₃ c₅ ∧ P₁ ∈ gam c₂ c₄ c₅ ∧ P₁ ∈ gam c₃ c₄ c₅) ∧
      (P₂ ∈ gam c₁ c₃ c₄ ∧ P₂ ∈ gam c₁ c₃ c₅ ∧ P₂ ∈ gam c₁ c₄ c₅ ∧ P₂ ∈ gam c₃ c₄ c₅) ∧
      (P₃ ∈ gam c₁ c₂ c₄ ∧ P₃ ∈ gam c₁ c₂ c₅ ∧ P₃ ∈ gam c₁ c₄ c₅ ∧ P₃ ∈ gam c₂ c₄ c₅) ∧
      (P₄ ∈ gam c₁ c₂ c₃ ∧ P₄ ∈ gam c₁ c₂ c₅ ∧ P₄ ∈ gam c₁ c₃ c₅ ∧ P₄ ∈ gam c₂ c₃ c₅) ∧
      (P₅ ∈ gam c₁ c₂ c₃ ∧ P₅ ∈ gam c₁ c₂ c₄ ∧ P₅ ∈ gam c₁ c₃ c₄ ∧ P₅ ∈ gam c₂ c₃ c₄) ∧
      (Cospherical ({P₁, P₂, P₃, P₄, P₅} : Set ℂ) ∨ Collinear ℝ ({P₁, P₂, P₃, P₄, P₅} : Set ℂ)) := by
  refine ⟨cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₄, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact cliffordPoint_mem_gams _ _ _ _ h23 h24 h25 h34 h35 h45 n234 n235 n245 n345
  · exact cliffordPoint_mem_gams _ _ _ _ h13 h14 h15 h34 h35 h45 n134 n135 n145 n345
  · exact cliffordPoint_mem_gams _ _ _ _ h12 h14 h15 h24 h25 h45 n124 n125 n145 n245
  · exact cliffordPoint_mem_gams _ _ _ _ h12 h13 h15 h23 h25 h35 n123 n125 n135 n235
  · exact cliffordPoint_mem_gams _ _ _ _ h12 h13 h14 h23 h24 h34 n123 n124 n134 n234
  · exact clifford_two_explicit _ _ _ _ _ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45 n123 n124 n125 n134 n135 n145 n234 n235 n245 n345

/-! ### n = 6 in `ℂ` -/

lemma conj_WW (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 : ℂ) :
    conj (WW a1 b1 a2 b2 a3 b3 a4 b4 a5 b5) = WW (conj a1) (conj b1) (conj a2) (conj b2) (conj a3) (conj b3) (conj a4) (conj b4) (conj a5) (conj b5) := by
  simp only [WW, map_add, map_sub, map_mul, map_neg, map_ofNat]

lemma conj_ZD (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : ℂ) :
    conj (ZD a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6) = ZD (conj a1) (conj b1) (conj a2) (conj b2) (conj a3) (conj b3) (conj a4) (conj b4) (conj a5) (conj b5) (conj a6) (conj b6) := by
  simp only [ZD, conj_WW, map_add, map_sub, map_mul, map_pow]

lemma conj_ZN (a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6 : ℂ) :
    conj (ZN a1 b1 a2 b2 a3 b3 a4 b4 a5 b5 a6 b6) = ZN (conj a1) (conj b1) (conj a2) (conj b2) (conj a3) (conj b3) (conj a4) (conj b4) (conj a5) (conj b5) (conj a6) (conj b6) := by
  simp only [ZN, conj_WW, map_add, map_sub, map_mul, map_pow]

/-- The common point of Clifford's third theorem (explicit). -/
noncomputable def cliffordPoint₃ (c₁ c₂ c₃ c₄ c₅ c₆ : ℂ) : ℂ :=
  ZN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆) / ZD c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)

lemma conj_cliffordPoint₃ (c₁ c₂ c₃ c₄ c₅ c₆ : ℂ) :
    conj (cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆) = ZN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ (conj c₅) c₅ (conj c₆) c₆ / ZD (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ (conj c₅) c₅ (conj c₆) c₆ := by
  unfold cliffordPoint₃
  rw [map_div₀, conj_ZN, conj_ZD]
  simp only [Complex.conj_conj]

/-- Shared setup for five circles: nonvanishing of the denominators. -/
lemma five_NN (c₁ c₂ c₃ c₄ c₅ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ)) :
    (NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) ≠ 0 ∧ NN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ ≠ 0) ∧
    (NN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₅ (conj c₅) ≠ 0 ∧ NN (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₅) c₅ ≠ 0) ∧
    (NN c₁ (conj c₁) c₂ (conj c₂) c₄ (conj c₄) c₅ (conj c₅) ≠ 0 ∧ NN (conj c₁) c₁ (conj c₂) c₂ (conj c₄) c₄ (conj c₅) c₅ ≠ 0) ∧
    (NN c₁ (conj c₁) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) ≠ 0 ∧ NN (conj c₁) c₁ (conj c₃) c₃ (conj c₄) c₄ (conj c₅) c₅ ≠ 0) ∧
    (NN c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) ≠ 0 ∧ NN (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ (conj c₅) c₅ ≠ 0) :=
  ⟨NN_ne_zero' h12 h13 h14 h23 h24 h34 n123, NN_ne_zero' h12 h13 h15 h23 h25 h35 n123,
    NN_ne_zero' h12 h14 h15 h24 h25 h45 n124, NN_ne_zero' h13 h14 h15 h34 h35 h45 n134,
    NN_ne_zero' h23 h24 h25 h34 h35 h45 n234⟩

/-- If three of the Clifford points of five circles are not collinear, then `WW ≠ 0`. -/
lemma WW_ne_zero_of (c₁ c₂ c₃ c₄ c₅ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))
    (hc : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ)) :
    WW c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) ≠ 0 := by
  obtain ⟨⟨N5, -⟩, ⟨N4, -⟩, -, -, -⟩ := five_NN c₁ c₂ c₃ c₄ c₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    n123 n124 n125 n134 n135 n145 n234 n235 n245 n345
  intro hW
  have e54 : cliffordPoint c₁ c₂ c₃ c₄ = cliffordPoint c₁ c₂ c₃ c₅ := eq_of_cross N5 N4 (cross54 ..) (by rw [hW, mul_zero])
  apply hc
  rw [e54, Set.insert_eq_of_mem (Set.mem_insert _ _)]
  exact collinear_pair ℝ _ _

/-- The common point `Q = ZN / ZD` lies on the circle through `P₅, P₄, P₃`. -/
lemma cliffordPoint₃_mem (c₁ c₂ c₃ c₄ c₅ c₆ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))
    (hc : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ))
    (hZ : ZD c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆) ≠ 0) :
    cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆ ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅) := by
  obtain ⟨⟨N5, N5'⟩, ⟨N4, N4'⟩, ⟨N3, N3'⟩, -, -⟩ := five_NN c₁ c₂ c₃ c₄ c₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    n123 n124 n125 n134 n135 n145 n234 n235 n245 n345
  have hZ' : ZD (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ (conj c₅) c₅ (conj c₆) c₆ ≠ 0 := by
    intro h0; apply hZ
    have := congrArg conj h0
    rw [conj_ZD, map_zero] at this
    simpa only [Complex.conj_conj] using this
  apply mem_circumcircle_of_TT hc
  rw [conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint₃]
  unfold cliffordPoint cliffordPoint₃
  exact TT_Q _ _ _ _ _ _ _ _ _ _ _ _ N5 N4 N3 N5' N4' N3' hZ hZ'

/-- The five Clifford points lie on the circle through `P₅, P₄, P₃` (when these are not collinear). -/
lemma five_mem_circumcircle (c₁ c₂ c₃ c₄ c₅ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0) (h24 : secondInter c₂ c₄ ≠ 0)
    (h25 : secondInter c₂ c₅ ≠ 0) (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))
    (hc : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ)) :
    ∀ P ∈ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₂ c₃ c₄ c₅} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅) := by
  obtain ⟨⟨N5, N5'⟩, ⟨N4, N4'⟩, ⟨N3, N3'⟩, ⟨N2, N2'⟩, ⟨N1, N1'⟩⟩ := five_NN c₁ c₂ c₃ c₄ c₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    n123 n124 n125 n134 n135 n145 n234 n235 n245 n345
  intro x hx
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl
  · exact mem_circumcircle_left _ _ _
  · exact mem_circumcircle_middle hc
  · exact mem_circumcircle_right hc
  · apply mem_circumcircle_of_TT hc
    rw [conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint]
    exact TT_five_2 _ _ _ _ _ _ _ _ _ _ N5 N4 N3 N2 N5' N4' N3' N2'
  · apply mem_circumcircle_of_TT hc
    rw [conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint]
    exact TT_five_1 _ _ _ _ _ _ _ _ _ _ N5 N4 N3 N1 N5' N4' N3' N1'

/-- The denominator of `cliffordPoint₃` does not vanish. -/
lemma ZD_ne_zero (c₁ c₂ c₃ c₄ c₅ c₆ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h16 : secondInter c₁ c₆ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0)
    (h24 : secondInter c₂ c₄ ≠ 0) (h25 : secondInter c₂ c₅ ≠ 0) (h26 : secondInter c₂ c₆ ≠ 0)
    (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0) (h36 : secondInter c₃ c₆ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0) (h46 : secondInter c₄ c₆ ≠ 0) (h56 : secondInter c₅ c₆ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n126 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₆, secondInter c₂ c₆} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n136 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₆, secondInter c₃ c₆} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n146 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₆, secondInter c₄ c₆} : Set ℂ))
    (n156 : ¬ Collinear ℝ ({secondInter c₁ c₅, secondInter c₁ c₆, secondInter c₅ c₆} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n236 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₆, secondInter c₃ c₆} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n246 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₆, secondInter c₄ c₆} : Set ℂ))
    (n256 : ¬ Collinear ℝ ({secondInter c₂ c₅, secondInter c₂ c₆, secondInter c₅ c₆} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))
    (n346 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₆, secondInter c₄ c₆} : Set ℂ))
    (n356 : ¬ Collinear ℝ ({secondInter c₃ c₅, secondInter c₃ c₆, secondInter c₅ c₆} : Set ℂ))
    (n456 : ¬ Collinear ℝ ({secondInter c₄ c₅, secondInter c₄ c₆, secondInter c₅ c₆} : Set ℂ))
    (m6 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ))
    (m5 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₄ c₆} : Set ℂ)) :
    ZD c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆) ≠ 0 := by
  obtain ⟨⟨N5, N5'⟩, ⟨N4, N4'⟩, ⟨N3, N3'⟩, -, -⟩ := five_NN c₁ c₂ c₃ c₄ c₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    n123 n124 n125 n134 n135 n145 n234 n235 n245 n345
  have W5 := WW_ne_zero_of c₁ c₂ c₃ c₄ c₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
    n123 n124 n125 n134 n135 n145 n234 n235 n245 n345 m6
  have W6 := WW_ne_zero_of c₁ c₂ c₃ c₄ c₆ h12 h13 h14 h16 h23 h24 h26 h34 h36 h46
    n123 n124 n126 n134 n136 n146 n234 n236 n246 n346 m5
  have hden := den3_ne_zero m6
  rw [conj_cliffordPoint, conj_cliffordPoint, conj_cliffordPoint] at hden
  unfold cliffordPoint at hden
  have d1 := conj_ne_zero_left h12
  have d2 := conj_ne_zero_right h12
  have d3 := conj_ne_zero_right h13
  have d4 := conj_ne_zero_right h14
  obtain ⟨-, -, e56⟩ := secondInter_ne_zero_iff' h56
  intro hZ
  have hZ' : ZD (conj c₁) c₁ (conj c₂) c₂ (conj c₃) c₃ (conj c₄) c₄ (conj c₅) c₅ (conj c₆) c₆ = 0 := by
    have := congrArg conj hZ
    rw [conj_ZD, map_zero] at this
    simpa only [Complex.conj_conj] using this
  have key := den3_of_ZD _ _ _ _ _ _ _ _ _ _ _ _ N5 N4 N3 N5' N4' N3' hZ hZ'
  have hNs := mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero N5 N4) N3) N5') N4') N3'
  have hZN : ZN c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆) = 0 := by
    rcases mul_eq_zero.1 ((mul_eq_zero.1 key).resolve_left (mul_ne_zero hden hNs)) with h | h
    · exact h
    · have := congrArg conj h
      rw [conj_ZN, map_zero] at this
      simpa only [Complex.conj_conj] using this
  have m := master c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)
  rw [hZ, hZN, mul_zero, mul_zero, sub_zero] at m
  exact (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero (mul_ne_zero d1 d2) d3) d4) W5) W6) e56) m.symm

/-- **Clifford's third circle theorem (n = 6).**
Six circles through `M = 0` (centres `c₁, …, c₆`) in general position: no two tangent at `M` or
coincident, the second intersection points of every triple not collinear, and — for every 5-subset `S` —
the Clifford points of `S` not degenerate to a line (three of them, hence all five, are not collinear).
For each 5-subset `S`, the five Clifford points `P_T` (`T ⊂ S`, `|T| = 4`, `P_T = cliffordPoint`, the
common point of the four `Γ` circles of `T`) lie on a circle `C_S` (Clifford's second theorem; here
`C_S` is the circumcircle of three of them).  Then the six circles `C_S` pass through a common point. -/
theorem clifford_three (c₁ c₂ c₃ c₄ c₅ c₆ : ℂ)
    (h12 : secondInter c₁ c₂ ≠ 0) (h13 : secondInter c₁ c₃ ≠ 0) (h14 : secondInter c₁ c₄ ≠ 0)
    (h15 : secondInter c₁ c₅ ≠ 0) (h16 : secondInter c₁ c₆ ≠ 0) (h23 : secondInter c₂ c₃ ≠ 0)
    (h24 : secondInter c₂ c₄ ≠ 0) (h25 : secondInter c₂ c₅ ≠ 0) (h26 : secondInter c₂ c₆ ≠ 0)
    (h34 : secondInter c₃ c₄ ≠ 0) (h35 : secondInter c₃ c₅ ≠ 0) (h36 : secondInter c₃ c₆ ≠ 0)
    (h45 : secondInter c₄ c₅ ≠ 0) (h46 : secondInter c₄ c₆ ≠ 0) (h56 : secondInter c₅ c₆ ≠ 0)
    (n123 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₃, secondInter c₂ c₃} : Set ℂ))
    (n124 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₄, secondInter c₂ c₄} : Set ℂ))
    (n125 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₅, secondInter c₂ c₅} : Set ℂ))
    (n126 : ¬ Collinear ℝ ({secondInter c₁ c₂, secondInter c₁ c₆, secondInter c₂ c₆} : Set ℂ))
    (n134 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₄, secondInter c₃ c₄} : Set ℂ))
    (n135 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₅, secondInter c₃ c₅} : Set ℂ))
    (n136 : ¬ Collinear ℝ ({secondInter c₁ c₃, secondInter c₁ c₆, secondInter c₃ c₆} : Set ℂ))
    (n145 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₅, secondInter c₄ c₅} : Set ℂ))
    (n146 : ¬ Collinear ℝ ({secondInter c₁ c₄, secondInter c₁ c₆, secondInter c₄ c₆} : Set ℂ))
    (n156 : ¬ Collinear ℝ ({secondInter c₁ c₅, secondInter c₁ c₆, secondInter c₅ c₆} : Set ℂ))
    (n234 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₄, secondInter c₃ c₄} : Set ℂ))
    (n235 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₅, secondInter c₃ c₅} : Set ℂ))
    (n236 : ¬ Collinear ℝ ({secondInter c₂ c₃, secondInter c₂ c₆, secondInter c₃ c₆} : Set ℂ))
    (n245 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₅, secondInter c₄ c₅} : Set ℂ))
    (n246 : ¬ Collinear ℝ ({secondInter c₂ c₄, secondInter c₂ c₆, secondInter c₄ c₆} : Set ℂ))
    (n256 : ¬ Collinear ℝ ({secondInter c₂ c₅, secondInter c₂ c₆, secondInter c₅ c₆} : Set ℂ))
    (n345 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₅, secondInter c₄ c₅} : Set ℂ))
    (n346 : ¬ Collinear ℝ ({secondInter c₃ c₄, secondInter c₃ c₆, secondInter c₄ c₆} : Set ℂ))
    (n356 : ¬ Collinear ℝ ({secondInter c₃ c₅, secondInter c₃ c₆, secondInter c₅ c₆} : Set ℂ))
    (n456 : ¬ Collinear ℝ ({secondInter c₄ c₅, secondInter c₄ c₆, secondInter c₅ c₆} : Set ℂ))
    (m6 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ))
    (m5 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₄ c₆} : Set ℂ))
    (m4 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₅ c₆} : Set ℂ))
    (m3 : ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₆, cliffordPoint c₁ c₂ c₅ c₆} : Set ℂ))
    (m2 : ¬ Collinear ℝ ({cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₆, cliffordPoint c₁ c₃ c₅ c₆} : Set ℂ))
    (m1 : ¬ Collinear ℝ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₂ c₃ c₄ c₆, cliffordPoint c₂ c₃ c₅ c₆} : Set ℂ)) :
    ∃ Q : ℂ,
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₂ c₃ c₄ c₅} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₄ c₆, cliffordPoint c₁ c₃ c₄ c₆, cliffordPoint c₂ c₃ c₄ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₄ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₄ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₆, cliffordPoint c₁ c₂ c₅ c₆, cliffordPoint c₁ c₃ c₅ c₆, cliffordPoint c₂ c₃ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₃ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₆, cliffordPoint c₁ c₂ c₅ c₆, cliffordPoint c₁ c₄ c₅ c₆, cliffordPoint c₂ c₄ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₂ c₄ c₅) (cliffordPoint c₁ c₂ c₄ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₂ c₄ c₅) (cliffordPoint c₁ c₂ c₄ c₆) (cliffordPoint c₁ c₂ c₅ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₆, cliffordPoint c₁ c₃ c₅ c₆, cliffordPoint c₁ c₄ c₅ c₆, cliffordPoint c₃ c₄ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₁ c₃ c₄ c₅) (cliffordPoint c₁ c₃ c₄ c₆) (cliffordPoint c₁ c₃ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₁ c₃ c₄ c₅) (cliffordPoint c₁ c₃ c₄ c₆) (cliffordPoint c₁ c₃ c₅ c₆)) ∧
      ((∀ P ∈ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₂ c₃ c₄ c₆, cliffordPoint c₂ c₃ c₅ c₆, cliffordPoint c₂ c₄ c₅ c₆, cliffordPoint c₃ c₄ c₅ c₆} : Set ℂ), P ∈ circumcircle (cliffordPoint c₂ c₃ c₄ c₅) (cliffordPoint c₂ c₃ c₄ c₆) (cliffordPoint c₂ c₃ c₅ c₆)) ∧
        Q ∈ circumcircle (cliffordPoint c₂ c₃ c₄ c₅) (cliffordPoint c₂ c₃ c₄ c₆) (cliffordPoint c₂ c₃ c₅ c₆)) := by
  have hZ := ZD_ne_zero c₁ c₂ c₃ c₄ c₅ c₆ h12 h13 h14 h15 h16 h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
    n123 n124 n125 n126 n134 n135 n136 n145 n146 n156 n234 n235 n236 n245 n246 n256 n345 n346 n356 n456 m6 m5
  refine ⟨cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine ⟨five_mem_circumcircle c₁ c₂ c₃ c₄ c₅ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
      n123 n124 n125 n134 n135 n145 n234 n235 n245 n345 m6, ?_⟩
    exact cliffordPoint₃_mem c₁ c₂ c₃ c₄ c₅ c₆ h12 h13 h14 h15 h23 h24 h25 h34 h35 h45
      n123 n124 n125 n134 n135 n145 n234 n235 n245 n345 m6 hZ
  · refine ⟨five_mem_circumcircle c₁ c₂ c₃ c₄ c₆ h12 h13 h14 h16 h23 h24 h26 h34 h36 h46
      n123 n124 n126 n134 n136 n146 n234 n236 n246 n346 m5, ?_⟩
    have e : cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆ = cliffordPoint₃ c₁ c₂ c₃ c₄ c₆ c₅ := by
      unfold cliffordPoint₃; rw [ZN_o5 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), ZD_o5 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), neg_div_neg_eq]
    rw [e]
    exact cliffordPoint₃_mem c₁ c₂ c₃ c₄ c₆ c₅ h12 h13 h14 h16 h23 h24 h26 h34 h36 h46
      n123 n124 n126 n134 n136 n146 n234 n236 n246 n346 m5 (by rw [ZD_o5 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)]; exact neg_ne_zero.2 hZ)
  · refine ⟨five_mem_circumcircle c₁ c₂ c₃ c₅ c₆ h12 h13 h15 h16 h23 h25 h26 h35 h36 h56
      n123 n125 n126 n135 n136 n156 n235 n236 n256 n356 m4, ?_⟩
    have e : cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆ = cliffordPoint₃ c₁ c₂ c₃ c₅ c₆ c₄ := by
      unfold cliffordPoint₃; rw [ZN_o4 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), ZD_o4 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)]
    rw [e]
    exact cliffordPoint₃_mem c₁ c₂ c₃ c₅ c₆ c₄ h12 h13 h15 h16 h23 h25 h26 h35 h36 h56
      n123 n125 n126 n135 n136 n156 n235 n236 n256 n356 m4 (by rw [ZD_o4 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)]; exact hZ)
  · refine ⟨five_mem_circumcircle c₁ c₂ c₄ c₅ c₆ h12 h14 h15 h16 h24 h25 h26 h45 h46 h56
      n124 n125 n126 n145 n146 n156 n245 n246 n256 n456 m3, ?_⟩
    have e : cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆ = cliffordPoint₃ c₁ c₂ c₄ c₅ c₆ c₃ := by
      unfold cliffordPoint₃; rw [ZN_o3 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), ZD_o3 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), neg_div_neg_eq]
    rw [e]
    exact cliffordPoint₃_mem c₁ c₂ c₄ c₅ c₆ c₃ h12 h14 h15 h16 h24 h25 h26 h45 h46 h56
      n124 n125 n126 n145 n146 n156 n245 n246 n256 n456 m3 (by rw [ZD_o3 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)]; exact neg_ne_zero.2 hZ)
  · refine ⟨five_mem_circumcircle c₁ c₃ c₄ c₅ c₆ h13 h14 h15 h16 h34 h35 h36 h45 h46 h56
      n134 n135 n136 n145 n146 n156 n345 n346 n356 n456 m2, ?_⟩
    have e : cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆ = cliffordPoint₃ c₁ c₃ c₄ c₅ c₆ c₂ := by
      unfold cliffordPoint₃; rw [ZN_o2 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), ZD_o2 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)]
    rw [e]
    exact cliffordPoint₃_mem c₁ c₃ c₄ c₅ c₆ c₂ h13 h14 h15 h16 h34 h35 h36 h45 h46 h56
      n134 n135 n136 n145 n146 n156 n345 n346 n356 n456 m2 (by rw [ZD_o2 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)]; exact hZ)
  · refine ⟨five_mem_circumcircle c₂ c₃ c₄ c₅ c₆ h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
      n234 n235 n236 n245 n246 n256 n345 n346 n356 n456 m1, ?_⟩
    have e : cliffordPoint₃ c₁ c₂ c₃ c₄ c₅ c₆ = cliffordPoint₃ c₂ c₃ c₄ c₅ c₆ c₁ := by
      unfold cliffordPoint₃; rw [ZN_o1 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), ZD_o1 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆), neg_div_neg_eq]
    rw [e]
    exact cliffordPoint₃_mem c₂ c₃ c₄ c₅ c₆ c₁ h23 h24 h25 h26 h34 h35 h36 h45 h46 h56
      n234 n235 n236 n245 n246 n256 n345 n346 n356 n456 m1 (by rw [ZD_o1 c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) c₆ (conj c₆)]; exact neg_ne_zero.2 hZ)

end Clifford
