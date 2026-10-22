import Clifford.Basic
import Clifford.Third

/-!
# Layer 15: classical-statement comparison

Layer 15. These definitions and statements were written independently, from textbook statements,
by an AI model that did not see this code; they are reproduced verbatim. Each cov_* theorem proves
(or proves part of) one of them from this development.
-/


/-!
# Paper D — classical statements D1–D7 (blind formalisation)

All statements live in the Euclidean plane `Pt := EuclideanSpace ℝ (Fin 2)`.
Constructed objects (second intersection points, Clifford points, Fermat points,
Thébault circles, auxiliary circumcentres, bisector feet) are passed in as data
together with their DEFINING property; well-definedness facts that are needed only
to make such data exist are stated separately as `_obligation` theorems.
-/

open EuclideanGeometry

noncomputable section

namespace Clifford.Classical

/-- The Euclidean plane. -/
abbrev Pt := EuclideanSpace ℝ (Fin 2)

/-! ## D1 — Clifford's circle theorems -/

/-- OWN DEFINITION. General position hypothesis of D1 for `n` circles `c i` through a
common point `M`: genuine circles (positive radius), pairwise distinct, `P i j` is a
second common point of `c i` and `c j` different from `M`, and for any three circles the
three second points are not collinear. (Since distinct circles meet in at most two points,
`P i j` is uniquely determined by these conditions.) -/
structure CliffordGP (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt) (P : Fin n → Fin n → Pt) :
    Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  second_mem : ∀ i j, i ≠ j → P i j ∈ c i ∧ P i j ∈ c j
  second_ne : ∀ i j, i ≠ j → P i j ≠ M
  noncollinear : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ Collinear ℝ {P i j, P i k, P j k}

/-- OWN DEFINITION. `X` lies on every circle `Γ_ijk` (through the non-collinear points
`P i j, P i k, P j k`) for `i, j, k` pairwise distinct in `S`. For `S` with four elements
this says that `X` is a common point of the four circles of D1(a) (a "Clifford point").
Because `P i j, P i k, P j k` are non-collinear, `Cospherical {P i j, P i k, P j k, X}`
means exactly that `X` lies on their (unique) circumcircle. -/
def OnAllGamma {n : ℕ} (P : Fin n → Fin n → Pt) (S : Finset (Fin n)) (X : Pt) : Prop :=
  ∀ i ∈ S, ∀ j ∈ S, ∀ k ∈ S, i ≠ j → i ≠ k → j ≠ k →
    Cospherical ({P i j, P i k, P j k, X} : Set Pt)

/-- D1(a), Clifford n = 4: the four circles `Γ_123, Γ_124, Γ_134, Γ_234` have a common
point. -/
def classical_D1_a (c : Fin 4 → Sphere Pt) (M : Pt) (P : Fin 4 → Fin 4 → Pt)
    (h : CliffordGP 4 c M P) : Prop := 
    ∃ X : Pt, OnAllGamma P Finset.univ X


/-- D1(b), Clifford n = 5: the five Clifford points `X l` (of the four circles obtained by
omitting circle `l`) lie on one circle. -/
def classical_D1_b (c : Fin 5 → Sphere Pt) (M : Pt) (P : Fin 5 → Fin 5 → Pt)
    (h : CliffordGP 5 c M P) (X : Fin 5 → Pt)
    (hX : ∀ l, OnAllGamma P (Finset.univ.erase l) (X l))
    -- EXTRA HYPOTHESIS: "general position" — the Clifford point of each four circles is
    -- well defined (the four Γ-circles have exactly one common point); otherwise "the
    -- point given by part (a)" is not determined.
    (hXu : ∀ l Y, OnAllGamma P (Finset.univ.erase l) Y → Y = X l)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical (range X) ∨ Collinear ℝ (range X)`
    -- ("circle or line", the inversive form).
    (hnc : ¬ Collinear ℝ (Set.range X)) : Prop := 
    Cospherical (Set.range X)


/-- D1(c), Clifford n = 6: for each `m`, the five Clifford points `X m l` (`l ≠ m`) of the
five circles other than `m` lie on a circle `C m` (part (b)); these six circles have a
common point. `X m l` is the Clifford point of the four circles other than `m, l`. -/
def classical_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) : Prop := 
    ∃ Y : Pt, ∀ m, Y ∈ C m


/-- OWN DEFINITION. Data of Clifford's chain for `n` circles `c i` through `M`, levels
indexed by subsets `S` of the circles: `circ S` (for `|S|` odd) is the circle and `pt S`
(for `|S|` even) the point attached to `S`.
* level 1: `circ {i} = c i`;
* level 2: `pt {i,j}` is the second intersection of `c i, c j` (≠ `M`);
* odd level `|S| = 2k+1 ≥ 3`: `circ S` passes through the `|S|` points `pt (S \ {i})`,
  which are not collinear (general position), so `circ S` is uniquely determined;
* even level `|S| = 2k ≥ 4`: `pt S` lies on the `|S|` circles `circ (S \ {i})` and is their
  unique common point (general position).
All levels strictly below `n` are part of the data/hypotheses (they are the lower
instances of the chain); the theorems below assert the top level `n`. -/
structure CliffordChain (n : ℕ) (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt) : Prop where
  radius_pos : ∀ i, 0 < (c i).radius
  through_M : ∀ i, M ∈ c i
  distinct : Function.Injective c
  level_one : ∀ i, circ {i} = c i
  level_two : ∀ S : Finset (Fin n), S.card = 2 →
    pt S ≠ M ∧ ∀ i ∈ S, pt S ∈ circ (S.erase i)
  odd_mem : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt (S.erase i) ∈ circ S
  odd_gp : ∀ S : Finset (Fin n), Odd S.card → 3 ≤ S.card → S.card < n →
    ¬ Collinear ℝ ((fun i => pt (S.erase i)) '' (S : Set (Fin n)))
  even_mem : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ i ∈ S, pt S ∈ circ (S.erase i)
  even_gp : ∀ S : Finset (Fin n), Even S.card → 4 ≤ S.card → S.card < n →
    ∀ Y : Pt, (∀ i ∈ S, Y ∈ circ (S.erase i)) → Y = pt S

/-- D1(d), Clifford's chain, even step (all even `n ≥ 4`): the `n` circles of level
`n - 1` pass through one common point.
(The case `n = 2` is the general-position hypothesis `level_two` itself.) -/
def classical_D1_d_even (n : ℕ) (hn : 4 ≤ n) (he : Even n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ) : Prop := 
    ∃ Y : Pt, ∀ i, Y ∈ circ (Finset.univ.erase i)


/-- D1(d), Clifford's chain, odd step (all odd `n ≥ 3`): the `n` points of level `n - 1`
lie on one circle. -/
def classical_D1_d_odd (n : ℕ) (hn : 3 ≤ n) (ho : Odd n)
    (c : Fin n → Sphere Pt) (M : Pt)
    (pt : Finset (Fin n) → Pt) (circ : Finset (Fin n) → Sphere Pt)
    (h : CliffordChain n c M pt circ)
    -- EXTRA HYPOTHESIS: the top-level points are not collinear ("one circle"). For `n = 3`
    -- this is exactly the non-collinearity hypothesis of (a).
    -- AMBIGUOUS: drop it and conclude `Cospherical … ∨ Collinear ℝ …` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range fun i => pt (Finset.univ.erase i))) : Prop := 
    Cospherical (Set.range fun i => pt (Finset.univ.erase i))


/-! ## D2 — Miquel's pentagram (five circles) theorem -/

/-- D2. Five lines `ℓ 0, …, ℓ 4` in general position (no two parallel, no three
concurrent), labelled in the cyclic order of the sides of the inner pentagon: its vertices
are `V i = ℓ i ∩ ℓ (i+1)`, the star points are `T i = ℓ (i-1) ∩ ℓ (i+1)`, and the outer
triangle `i` (bounded by `ℓ (i-1), ℓ i, ℓ (i+1)`) has vertices `V (i-1), V i, T i` and
circumcircle `ω i`.
AMBIGUOUS: the labelling is only required to be cyclic as above; we do not additionally
require the inner pentagon to be convex / the figure to be a "star" (alternative: add a
hypothesis that the `V i` form a convex pentagon with the `T i` outside it).
Consecutive circles `ω i, ω (i+1)` meet in the inner vertex `V i` and in
a second point `Q i`. Then the five points `Q i` lie on one circle. -/
def classical_D2 (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k)
    (V T : Fin 5 → Pt)
    (hV : ∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1))
    (hT : ∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1))
    (ω : Fin 5 → Sphere Pt)
    (hω : ∀ i, V (i - 1) ∈ ω i ∧ V i ∈ ω i ∧ T i ∈ ω i)
    (Q : Fin 5 → Pt)
    -- The classical statement presupposes a second point; AMBIGUOUS: if `ω i, ω (i+1)` are
    -- tangent at `V i` one could take `Q i = V i` (here such configurations are excluded by
    -- the requirement `Q i ≠ V i`).
    (hQ : ∀ i, Q i ∈ ω i ∧ Q i ∈ ω (i + 1) ∧ Q i ≠ V i)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical ∨ Collinear` (circle or line).
    (hnc : ¬ Collinear ℝ (Set.range Q)) : Prop := 
    Cospherical (Set.range Q)


/-- D2 obligation (well-formedness only): for five lines in general position the
intersection points `V i`, `T i` exist and the three vertices of each outer triangle are
non-collinear, so the circumcircles `ω i` exist (and are unique). -/
def classical_D2_obligation (ℓ : Fin 5 → AffineSubspace ℝ Pt)
    (hℓ : ∀ i, Module.finrank ℝ (ℓ i).direction = 1)
    (hpar : ∀ i j, i ≠ j → ¬ (ℓ i).Parallel (ℓ j))
    (hconc : ∀ i j k, i ≠ j → i ≠ k → j ≠ k → ¬ ∃ p, p ∈ ℓ i ∧ p ∈ ℓ j ∧ p ∈ ℓ k) : Prop := 
    ∃ V T : Fin 5 → Pt, (∀ i, V i ∈ ℓ i ∧ V i ∈ ℓ (i + 1)) ∧
      (∀ i, T i ∈ ℓ (i - 1) ∧ T i ∈ ℓ (i + 1)) ∧
      ∀ i, ¬ Collinear ℝ ({V (i - 1), V i, T i} : Set Pt)


/-! ## D3 — Lester's theorem -/

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected OUTWARDLY on side
`q r` of triangle `p q r` (opposite side of line `q r` from `p`). -/
def IsOuterApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SOppSide p X

/-- OWN DEFINITION. `X` is the apex of the equilateral triangle erected INWARDLY on side
`q r` of triangle `p q r` (same side of line `q r` as `p`). -/
def IsInnerApex (p q r X : Pt) : Prop :=
  dist q X = dist q r ∧ dist r X = dist q r ∧ (line[ℝ, q, r]).SSameSide p X

/-- OWN DEFINITION. First Fermat point (first isogonic centre): common point of the lines
joining each vertex to the apex of the outward equilateral triangle on the opposite side. -/
def IsFirstFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsOuterApex a b c A' ∧ IsOuterApex b c a B' ∧ IsOuterApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- OWN DEFINITION. Second Fermat point (second isogonic centre): same with the inward
equilateral triangles. -/
def IsSecondFermatPoint (a b c F : Pt) : Prop :=
  ∃ A' B' C' : Pt, IsInnerApex a b c A' ∧ IsInnerApex b c a B' ∧ IsInnerApex c a b C' ∧
    F ∈ line[ℝ, a, A'] ∧ F ∈ line[ℝ, b, B'] ∧ F ∈ line[ℝ, c, C']

/-- D3, Lester's theorem: in a scalene triangle the two Fermat points, the circumcentre and
the nine-point centre are concyclic. -/
def classical_D3 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b)
    (F₁ F₂ : Pt) (hF₁ : IsFirstFermatPoint a b c F₁) (hF₂ : IsSecondFermatPoint a b c F₂) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    Cospherical ({F₁, F₂, t.circumcenter, (t.ninePointCircle).center} : Set Pt)


/-- D3 obligation (well-formedness only): both Fermat points exist (the second one needs
the triangle not to be equilateral; scalene suffices). -/
def classical_D3_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hab : dist a b ≠ dist b c) (hbc : dist b c ≠ dist c a) (hca : dist c a ≠ dist a b) : Prop := 
    (∃ F, IsFirstFermatPoint a b c F) ∧ (∃ F, IsSecondFermatPoint a b c F)


/-! ## D4 — Sawayama–Thébault theorem -/

/-- OWN DEFINITION. The circle `ω` (positive radius) is tangent to the line `p q`. -/
def TangentToLine (ω : Sphere Pt) (p q : Pt) : Prop :=
  0 < ω.radius ∧ Metric.infDist ω.center (line[ℝ, p, q] : Set Pt) = ω.radius

/-- OWN DEFINITION. The circle `ω` (positive radius) is internally tangent to the circle `Ω`
(lies inside `Ω` and touches it). -/
def InternallyTangent (ω Ω : Sphere Pt) : Prop :=
  0 < ω.radius ∧ ω.radius < Ω.radius ∧ dist ω.center Ω.center = Ω.radius - ω.radius

/-- D4, Sawayama–Thébault: `D` on side `BC`; `ω₁, ω₂` are tangent to lines `AD`, `BC`,
internally tangent to the circumcircle, one on each side of `AD`. Then their centres and
the incentre are collinear. -/
def classical_D4 (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    -- AMBIGUOUS: "on side BC" taken as strictly between `B` and `C` (`Wbtw` would allow
    -- `D = B` or `D = C`, where one of the two circles degenerates).
    (hd : Sbtw ℝ b d c)
    (ω₁ ω₂ : Sphere Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    TangentToLine ω₁ a d → TangentToLine ω₁ b c → InternallyTangent ω₁ t.circumsphere →
    TangentToLine ω₂ a d → TangentToLine ω₂ b c → InternallyTangent ω₂ t.circumsphere →
    (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center →
    -- EXTRA HYPOTHESIS / AMBIGUOUS: the two circles lie on the same side of `BC` as `A`
    -- (inside the angles `ADB` and `ADC`). Without it, each side of `AD` also carries a
    -- circle in the circular segment cut off by `BC`, for which the statement is not the
    -- classical one.
    (line[ℝ, b, c]).SSameSide ω₁.center a → (line[ℝ, b, c]).SSameSide ω₂.center a →
    Collinear ℝ ({ω₁.center, ω₂.center, t.incenter} : Set Pt)


/-- D4 obligation (well-formedness only): the two Thébault circles exist. -/
def classical_D4_obligation (a b c d : Pt) (h : AffineIndependent ℝ ![a, b, c])
    (hd : Sbtw ℝ b d c) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ∃ ω₁ ω₂ : Sphere Pt,
      TangentToLine ω₁ a d ∧ TangentToLine ω₁ b c ∧ InternallyTangent ω₁ t.circumsphere ∧
      TangentToLine ω₂ a d ∧ TangentToLine ω₂ b c ∧ InternallyTangent ω₂ t.circumsphere ∧
      (line[ℝ, a, d]).SOppSide ω₁.center ω₂.center ∧
      (line[ℝ, b, c]).SSameSide ω₁.center a ∧ (line[ℝ, b, c]).SSameSide ω₂.center a


/-! ## D5 — Kosnita's theorem -/

/-- OWN DEFINITION. `o` is equidistant from `p, q, r`, i.e. (for `p, q, r` not collinear) the
circumcentre of triangle `p q r`. -/
def IsCircumcenterOf (o p q r : Pt) : Prop :=
  dist o p = dist o q ∧ dist o p = dist o r

/-- D5, Kosnita: with `O` the circumcentre and `O_a, O_b, O_c` the circumcentres of `OBC`,
`OCA`, `OAB`, the lines `AO_a, BO_b, CO_c` are concurrent.
(If `O` lies on a side — right triangle — the corresponding `O_x` does not exist and the
statement is vacuous; see the obligation.) -/
def classical_D5 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (Oa Ob Oc : Pt) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    IsCircumcenterOf Oa t.circumcenter b c → IsCircumcenterOf Ob t.circumcenter c a →
    IsCircumcenterOf Oc t.circumcenter a b →
    -- EXTRA HYPOTHESIS: the three lines are defined (`A ≠ O_a` etc.; `A = O_a` happens e.g.
    -- for an isosceles triangle with apex angle 120° at `A`).
    a ≠ Oa → b ≠ Ob → c ≠ Oc →
    -- AMBIGUOUS: concurrency "at infinity" allowed — the Kosnita point (isogonal conjugate
    -- of the nine-point centre) is at infinity when the nine-point centre lies on the
    -- circumcircle; then the three lines are parallel. Strict alternative: add the
    -- hypothesis that the lines are not all parallel and keep only the first disjunct.
    (∃ X : Pt, X ∈ line[ℝ, a, Oa] ∧ X ∈ line[ℝ, b, Ob] ∧ X ∈ line[ℝ, c, Oc]) ∨
      ((line[ℝ, a, Oa]).Parallel (line[ℝ, b, Ob]) ∧
        (line[ℝ, b, Ob]).Parallel (line[ℝ, c, Oc]))


/-- D5 obligation (well-formedness only): if the circumcentre is not on line `BC`, the
circumcentre of `OBC` exists. -/
def classical_D5_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    ¬ Collinear ℝ ({t.circumcenter, b, c} : Set Pt) →
      ∃ Oa, IsCircumcenterOf Oa t.circumcenter b c


/-! ## D6 — Blundon's fundamental inequality -/

/-- D6, Blundon, lower bound. -/
def classical_D6_lower (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    2 * R ^ 2 + 10 * R * r - r ^ 2 - 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r) ≤ s ^ 2


/-- D6, Blundon, upper bound. -/
def classical_D6_upper (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    let R := t.circumradius
    let r := t.inradius
    let s := (dist a b + dist b c + dist c a) / 2
    s ^ 2 ≤ 2 * R ^ 2 + 10 * R * r - r ^ 2 + 2 * (R - 2 * r) * Real.sqrt (R ^ 2 - 2 * R * r)


/-- D6 obligation (well-formedness only): the radicand is non-negative (Euler `R ≥ 2r`),
so `Real.sqrt` is the genuine square root rather than its junk value `0`. -/
def classical_D6_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    let t : Affine.Triangle ℝ Pt := ⟨![a, b, c], h⟩
    0 ≤ t.circumradius ^ 2 - 2 * t.circumradius * t.inradius


/-! ## D7 — Steiner–Lehmus theorem -/

/-- OWN DEFINITION. `e` is the foot of the internal bisector from vertex `v` of the angle
`p v q`: `e` lies on segment `p q` and bisects the angle at `v`. -/
def IsBisectorFoot (v p q e : Pt) : Prop :=
  Wbtw ℝ p e q ∧ ∠ p v e = ∠ e v q

/-- D7, Steiner–Lehmus: if the internal bisectors from `B` and `C` (vertex to opposite side)
have equal length, then `AB = AC`. -/
def classical_D7 (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) (e f : Pt)
    (he : IsBisectorFoot b a c e) (hf : IsBisectorFoot c a b f)
    (hlen : dist b e = dist c f) : Prop := 
    dist a b = dist a c


/-- D7 obligation (well-formedness only): the bisector foot exists. -/
def classical_D7_obligation (a b c : Pt) (h : AffineIndependent ℝ ![a, b, c]) : Prop := 
    ∃ e, IsBisectorFoot b a c e


end Clifford.Classical

namespace Clifford.Classical

noncomputable def planeIso : ℂ ≃ₗᵢ[ℝ] Pt := Complex.orthonormalBasisOneI.repr
noncomputable def complexIso : Pt ≃ₗᵢ[ℝ] ℂ := planeIso.symm

 theorem cov_cospherical_transport {s : Set Pt} :
    Cospherical (complexIso '' s) ↔ Cospherical s := by
  constructor
  · rintro ⟨o, r, hr⟩
    refine ⟨complexIso.symm o, r, fun p hp => ?_⟩
    have hh := hr (complexIso p) ⟨p, hp, rfl⟩
    rw [← complexIso.apply_symm_apply o, complexIso.dist_map] at hh
    exact hh
  · rintro ⟨o, r, hr⟩
    refine ⟨complexIso o, r, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    rw [complexIso.dist_map]
    exact hr p hp

 theorem cov_collinear_transport {s : Set Pt} :
    Collinear ℝ (complexIso '' s) ↔ Collinear ℝ s := by
  rw [collinear_iff_exists_forall_eq_smul_vadd, collinear_iff_exists_forall_eq_smul_vadd]
  constructor
  · rintro ⟨o, v, h⟩
    refine ⟨complexIso.symm o, complexIso.symm v, fun p hp => ?_⟩
    obtain ⟨r, hr⟩ := h (complexIso p) ⟨p, hp, rfl⟩
    refine ⟨r, ?_⟩
    have hh := congrArg complexIso.symm hr
    simpa only [vadd_eq_add, map_add, map_smul, LinearIsometryEquiv.symm_apply_apply] using hh
  · rintro ⟨o, v, h⟩
    refine ⟨complexIso o, complexIso v, ?_⟩
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨r, rfl⟩ := h p hp
    exact ⟨r, by simp [vadd_eq_add]⟩

open ComplexConjugate
noncomputable def normalizeAt (M : Pt) : Pt ≃ᵃⁱ[ℝ] ℂ :=
  (AffineIsometryEquiv.vaddConst ℝ M).symm.trans complexIso.toAffineIsometryEquiv

 theorem cov_cospherical_affine (f : Pt ≃ᵃⁱ[ℝ] ℂ) {s : Set Pt} :
    Cospherical (f '' s) ↔ Cospherical s := by
  constructor
  · rintro ⟨o,r,hr⟩
    refine ⟨f.symm o,r,fun p hp => ?_⟩
    have hh := hr (f p) ⟨p,hp,rfl⟩
    rw [← f.apply_symm_apply o, f.dist_map] at hh
    exact hh
  · rintro ⟨o,r,hr⟩
    refine ⟨f o,r,?_⟩
    rintro _ ⟨p,hp,rfl⟩
    rw [f.dist_map]
    exact hr p hp

 theorem cov_second_unique (a b z : ℂ) (hab : a ≠ b) (hz : z ≠ 0)
    (ha : dist z a = ‖a‖) (hb : dist z b = ‖b‖) : z = Clifford.secondInter a b := by
  have ha' : z * conj z = conj a * z + a * conj z := by
    have hh := (Clifford.dist_eq_dist_iff z 0 a).1 (by simpa using ha)
    simp only [map_sub, map_zero] at hh
    linear_combination hh
  have hb' : z * conj z = conj b * z + b * conj z := by
    have hh := (Clifford.dist_eq_dist_iff z 0 b).1 (by simpa using hb)
    simp only [map_sub, map_zero] at hh
    linear_combination hh
  have hden : conj a - conj b ≠ 0 := sub_ne_zero.2 (fun he => hab ((starRingEnd ℂ).injective he))
  have hh : conj z * (z * (conj a - conj b) - (conj a * b - a * conj b)) = 0 := by
    linear_combination (conj a - conj b) * ha' + conj a * (hb' - ha')
  have hz' : conj z ≠ 0 := by simpa using hz
  have he := (mul_eq_zero.1 hh).resolve_left hz'
  rw [Clifford.secondInter, Clifford.sec, eq_div_iff hden]
  exact sub_eq_zero.1 he

 theorem cov_gp_normalize {n : ℕ} (c : Fin n → Sphere Pt) (M : Pt)
    (P : Fin n → Fin n → Pt) (h : CliffordGP n c M P) :
    ∀ i j, i ≠ j → normalizeAt M (P i j) =
      Clifford.secondInter (normalizeAt M (c i).center) (normalizeAt M (c j).center) := by
  intro i j hij
  let f := normalizeAt M
  have hzero : f M = 0 := by simp [f,normalizeAt]
  have hr : ∀ i, ‖f (c i).center‖ = (c i).radius := by
    intro k
    have hh := h.through_M k
    change dist M (c k).center = (c k).radius at hh
    rw [← f.dist_map, hzero, dist_zero_left] at hh
    exact hh
  apply cov_second_unique
  · intro he
    have he' := f.injective he
    apply h.distinct.ne hij
    apply Sphere.ext
    · exact he'
    · rw [← hr i, ← hr j, he]
  · intro he
    exact h.second_ne i j hij (f.injective (he.trans hzero.symm))
  · rw [f.dist_map, hr i]
    exact (h.second_mem i j hij).1
  · rw [f.dist_map, hr j]
    exact (h.second_mem i j hij).2

 theorem cov_collinear_affine (f : Pt ≃ᵃⁱ[ℝ] ℂ) {s : Set Pt} :
    Collinear ℝ (f '' s) ↔ Collinear ℝ s := by
  rw [collinear_iff_exists_forall_eq_smul_vadd, collinear_iff_exists_forall_eq_smul_vadd]
  constructor
  · rintro ⟨o,v,h⟩
    refine ⟨f.symm o,f.symm.linearIsometryEquiv v,fun p hp => ?_⟩
    obtain ⟨r,hr⟩ := h (f p) ⟨p,hp,rfl⟩
    refine ⟨r,?_⟩
    have hh := congrArg f.symm hr
    simpa only [f.symm_apply_apply, f.symm.map_vadd, map_smul] using hh
  · rintro ⟨o,v,h⟩
    refine ⟨f o,f.linearIsometryEquiv v,?_⟩
    rintro _ ⟨p,hp,rfl⟩
    obtain ⟨r,rfl⟩ := h p hp
    exact ⟨r, by rw [f.map_vadd, map_smul]⟩

 theorem cov_gam_cospherical {a b c X : ℂ}
    (hn : ¬ Collinear ℝ {Clifford.secondInter a b,Clifford.secondInter a c,Clifford.secondInter b c})
    (hx : X ∈ Clifford.gam a b c) :
    Cospherical {Clifford.secondInter a b,Clifford.secondInter a c,Clifford.secondInter b c,X} := by
  apply (Clifford.gam a b c).cospherical.subset
  intro p hp
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hp
  rcases hp with rfl|rfl|rfl|rfl
  · exact Clifford.mem_circumcircle_left _ _ _
  · exact Clifford.mem_circumcircle_middle hn
  · exact Clifford.mem_circumcircle_right hn
  · exact hx

/-- Part of `cov_D1_a` (case analysis for vertex `0`), split off to keep each proof small. -/
theorem cov_D1_a_vertex0 (z : Fin 4 → ℂ) (X : ℂ)
    (h123 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 2),
      Clifford.secondInter (z 1) (z 2),X})
    (h124 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 1) (z 3),X})
    (h134 : Cospherical {Clifford.secondInter (z 0) (z 2),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (h234 : Cospherical {Clifford.secondInter (z 1) (z 2),Clifford.secondInter (z 1) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (j k : Fin 4) (hij : (0 : Fin 4) ≠ j) (hik : (0 : Fin 4) ≠ k) (hjk : j ≠ k) :
    Cospherical {Clifford.secondInter (z 0) (z j),Clifford.secondInter (z 0) (z k),
      Clifford.secondInter (z j) (z k),X} := by
  fin_cases j <;> fin_cases k <;> simp at hij hik hjk
  all_goals simp only [show (⟨0,by decide⟩ : Fin 4) = 0 from rfl,
    show (⟨1,by decide⟩ : Fin 4) = 1 from rfl,
    show (⟨2,by decide⟩ : Fin 4) = 2 from rfl,
    show (⟨3,by decide⟩ : Fin 4) = 3 from rfl]
  all_goals first
    | (convert h123 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 2) (z 0),
        Clifford.secondInter_symm (z 2) (z 1)]; tauto))
    | (convert h124 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 1)]; tauto))
    | (convert h134 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))
    | (convert h234 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 1), Clifford.secondInter_symm (z 3) (z 1),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))

/-- Part of `cov_D1_a` (case analysis for vertex `1`), split off to keep each proof small. -/
theorem cov_D1_a_vertex1 (z : Fin 4 → ℂ) (X : ℂ)
    (h123 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 2),
      Clifford.secondInter (z 1) (z 2),X})
    (h124 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 1) (z 3),X})
    (h134 : Cospherical {Clifford.secondInter (z 0) (z 2),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (h234 : Cospherical {Clifford.secondInter (z 1) (z 2),Clifford.secondInter (z 1) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (j k : Fin 4) (hij : (1 : Fin 4) ≠ j) (hik : (1 : Fin 4) ≠ k) (hjk : j ≠ k) :
    Cospherical {Clifford.secondInter (z 1) (z j),Clifford.secondInter (z 1) (z k),
      Clifford.secondInter (z j) (z k),X} := by
  fin_cases j <;> fin_cases k <;> simp at hij hik hjk
  all_goals simp only [show (⟨0,by decide⟩ : Fin 4) = 0 from rfl,
    show (⟨1,by decide⟩ : Fin 4) = 1 from rfl,
    show (⟨2,by decide⟩ : Fin 4) = 2 from rfl,
    show (⟨3,by decide⟩ : Fin 4) = 3 from rfl]
  all_goals first
    | (convert h123 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 2) (z 0),
        Clifford.secondInter_symm (z 2) (z 1)]; tauto))
    | (convert h124 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 1)]; tauto))
    | (convert h134 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))
    | (convert h234 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 1), Clifford.secondInter_symm (z 3) (z 1),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))

/-- Part of `cov_D1_a` (case analysis for vertex `2`), split off to keep each proof small. -/
theorem cov_D1_a_vertex2 (z : Fin 4 → ℂ) (X : ℂ)
    (h123 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 2),
      Clifford.secondInter (z 1) (z 2),X})
    (h124 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 1) (z 3),X})
    (h134 : Cospherical {Clifford.secondInter (z 0) (z 2),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (h234 : Cospherical {Clifford.secondInter (z 1) (z 2),Clifford.secondInter (z 1) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (j k : Fin 4) (hij : (2 : Fin 4) ≠ j) (hik : (2 : Fin 4) ≠ k) (hjk : j ≠ k) :
    Cospherical {Clifford.secondInter (z 2) (z j),Clifford.secondInter (z 2) (z k),
      Clifford.secondInter (z j) (z k),X} := by
  fin_cases j <;> fin_cases k <;> simp at hij hik hjk
  all_goals simp only [show (⟨0,by decide⟩ : Fin 4) = 0 from rfl,
    show (⟨1,by decide⟩ : Fin 4) = 1 from rfl,
    show (⟨2,by decide⟩ : Fin 4) = 2 from rfl,
    show (⟨3,by decide⟩ : Fin 4) = 3 from rfl]
  all_goals first
    | (convert h123 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 2) (z 0),
        Clifford.secondInter_symm (z 2) (z 1)]; tauto))
    | (convert h124 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 1)]; tauto))
    | (convert h134 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))
    | (convert h234 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 1), Clifford.secondInter_symm (z 3) (z 1),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))

/-- Part of `cov_D1_a` (case analysis for vertex `3`), split off to keep each proof small. -/
theorem cov_D1_a_vertex3 (z : Fin 4 → ℂ) (X : ℂ)
    (h123 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 2),
      Clifford.secondInter (z 1) (z 2),X})
    (h124 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 1) (z 3),X})
    (h134 : Cospherical {Clifford.secondInter (z 0) (z 2),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (h234 : Cospherical {Clifford.secondInter (z 1) (z 2),Clifford.secondInter (z 1) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (j k : Fin 4) (hij : (3 : Fin 4) ≠ j) (hik : (3 : Fin 4) ≠ k) (hjk : j ≠ k) :
    Cospherical {Clifford.secondInter (z 3) (z j),Clifford.secondInter (z 3) (z k),
      Clifford.secondInter (z j) (z k),X} := by
  fin_cases j <;> fin_cases k <;> simp at hij hik hjk
  all_goals simp only [show (⟨0,by decide⟩ : Fin 4) = 0 from rfl,
    show (⟨1,by decide⟩ : Fin 4) = 1 from rfl,
    show (⟨2,by decide⟩ : Fin 4) = 2 from rfl,
    show (⟨3,by decide⟩ : Fin 4) = 3 from rfl]
  all_goals first
    | (convert h123 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 2) (z 0),
        Clifford.secondInter_symm (z 2) (z 1)]; tauto))
    | (convert h124 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 1) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 1)]; tauto))
    | (convert h134 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 0), Clifford.secondInter_symm (z 3) (z 0),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))
    | (convert h234 using 1 <;> (ext p; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z 2) (z 1), Clifford.secondInter_symm (z 3) (z 1),
        Clifford.secondInter_symm (z 3) (z 2)]; tauto))

/-- Part of `cov_D1_a`: every ordered triple of the four circles. -/
theorem cov_D1_a_triples (z : Fin 4 → ℂ) (X : ℂ)
    (h123 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 2),
      Clifford.secondInter (z 1) (z 2),X})
    (h124 : Cospherical {Clifford.secondInter (z 0) (z 1),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 1) (z 3),X})
    (h134 : Cospherical {Clifford.secondInter (z 0) (z 2),Clifford.secondInter (z 0) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (h234 : Cospherical {Clifford.secondInter (z 1) (z 2),Clifford.secondInter (z 1) (z 3),
      Clifford.secondInter (z 2) (z 3),X})
    (i j k : Fin 4) (hij : i ≠ j) (hik : i ≠ k) (hjk : j ≠ k) :
    Cospherical {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
      Clifford.secondInter (z j) (z k),X} := by
  fin_cases i
  · exact cov_D1_a_vertex0 z X h123 h124 h134 h234 j k hij hik hjk
  · exact cov_D1_a_vertex1 z X h123 h124 h134 h234 j k hij hik hjk
  · exact cov_D1_a_vertex2 z X h123 h124 h134 h234 j k hij hik hjk
  · exact cov_D1_a_vertex3 z X h123 h124 h134 h234 j k hij hik hjk

theorem cov_D1_a (c : Fin 4 → Sphere Pt) (M : Pt) (P : Fin 4 → Fin 4 → Pt)
    (h : CliffordGP 4 c M P) :
    ∃ X : Pt, OnAllGamma P Finset.univ X := by
  let f := normalizeAt M
  let z : Fin 4 → ℂ := fun i => f (c i).center
  have he : ∀ i j, i ≠ j → f (P i j) = Clifford.secondInter (z i) (z j) :=
    cov_gp_normalize c M P h
  have hz : ∀ i j, i ≠ j → Clifford.secondInter (z i) (z j) ≠ 0 := by
    intro i j hij hh
    have hh' : f (P i j) = 0 := (he i j hij).trans hh
    have hzero : f M = 0 := by simp [f,normalizeAt]
    exact h.second_ne i j hij (f.injective (hh'.trans hzero.symm))
  have hn : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
        Clifford.secondInter (z j) (z k)} := by
    intro i j k hij hik hjk hh
    apply h.noncollinear i j k hij hik hjk
    apply (cov_collinear_affine f).1
    simpa only [Set.image_insert_eq,Set.image_singleton,he i j hij,he i k hik,he j k hjk] using hh
  obtain ⟨X,h1,h2,h3,h4⟩ := Clifford.clifford_one (z 0) (z 1) (z 2) (z 3)
    (hz 0 1 (by decide)) (hz 0 2 (by decide)) (hz 0 3 (by decide))
    (hz 1 2 (by decide)) (hz 1 3 (by decide)) (hz 2 3 (by decide))
    (hn 0 1 2 (by decide) (by decide) (by decide))
    (hn 0 1 3 (by decide) (by decide) (by decide))
    (hn 0 2 3 (by decide) (by decide) (by decide))
    (hn 1 2 3 (by decide) (by decide) (by decide))
  have h123 := cov_gam_cospherical (hn 0 1 2 (by decide) (by decide) (by decide)) h1
  have h124 := cov_gam_cospherical (hn 0 1 3 (by decide) (by decide) (by decide)) h2
  have h134 := cov_gam_cospherical (hn 0 2 3 (by decide) (by decide) (by decide)) h3
  have h234 := cov_gam_cospherical (hn 1 2 3 (by decide) (by decide) (by decide)) h4
  refine ⟨f.symm X,?_⟩
  intro i _ j _ k _ hij hik hjk
  apply (cov_cospherical_affine f).1
  simp only [Set.image_insert_eq,Set.image_singleton,f.apply_symm_apply,he i j hij,he i k hik,he j k hjk]
  exact cov_D1_a_triples z X h123 h124 h134 h234 i j k hij hik hjk


theorem cov_gamma_of_four {z : Fin 5 → ℂ} {Y : ℂ} (a b c d : Fin 5)
    (hn : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
        Clifford.secondInter (z j) (z k)})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : Y ∈ Clifford.gam (z a) (z b) (z c))
    (h2 : Y ∈ Clifford.gam (z a) (z b) (z d))
    (h3 : Y ∈ Clifford.gam (z a) (z c) (z d))
    (h4 : Y ∈ Clifford.gam (z b) (z c) (z d)) :
    ∀ i ∈ ({a,b,c,d} : Set (Fin 5)), ∀ j ∈ ({a,b,c,d} : Set (Fin 5)),
      ∀ k ∈ ({a,b,c,d} : Set (Fin 5)), i ≠ j → i ≠ k → j ≠ k →
      Cospherical {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
        Clifford.secondInter (z j) (z k),Y} := by
  have h123 := cov_gam_cospherical (hn a b c hab hac hbc) h1
  have h124 := cov_gam_cospherical (hn a b d hab had hbd) h2
  have h134 := cov_gam_cospherical (hn a c d hac had hcd) h3
  have h234 := cov_gam_cospherical (hn b c d hbc hbd hcd) h4
  have hs : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      Cospherical {Clifford.secondInter (z (![a,b,c,d] i)) (z (![a,b,c,d] j)),
        Clifford.secondInter (z (![a,b,c,d] i)) (z (![a,b,c,d] k)),
        Clifford.secondInter (z (![a,b,c,d] j)) (z (![a,b,c,d] k)),Y} := by
    intro i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hik hjk
    all_goals simp only [show (⟨0,by decide⟩ : Fin 4) = 0 from rfl,
      show (⟨1,by decide⟩ : Fin 4) = 1 from rfl,
      show (⟨2,by decide⟩ : Fin 4) = 2 from rfl,
      show (⟨3,by decide⟩ : Fin 4) = 3 from rfl,
      show (![a,b,c,d] (0 : Fin 4)) = a from rfl,
      show (![a,b,c,d] (1 : Fin 4)) = b from rfl,
      show (![a,b,c,d] (2 : Fin 4)) = c from rfl,
      show (![a,b,c,d] (3 : Fin 4)) = d from rfl]
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
  intro i hi j hj k hk hij hik hjk
  have he : ∀ q ∈ ({a,b,c,d} : Set (Fin 5)), ∃ t : Fin 4, ![a,b,c,d] t = q := by
    intro q hq
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  obtain ⟨i',rfl⟩ := he i hi
  obtain ⟨j',rfl⟩ := he j hj
  obtain ⟨k',rfl⟩ := he k hk
  exact hs i' j' k' (fun hh => hij (hh ▸ rfl)) (fun hh => hik (hh ▸ rfl))
    (fun hh => hjk (hh ▸ rfl))

theorem cov_D1_b (c : Fin 5 → Sphere Pt) (M : Pt) (P : Fin 5 → Fin 5 → Pt)
    (h : CliffordGP 5 c M P) (X : Fin 5 → Pt)
    (hX : ∀ l, OnAllGamma P (Finset.univ.erase l) (X l))
    -- EXTRA HYPOTHESIS: "general position" — the Clifford point of each four circles is
    -- well defined (the four Γ-circles have exactly one common point); otherwise "the
    -- point given by part (a)" is not determined.
    (hXu : ∀ l Y, OnAllGamma P (Finset.univ.erase l) Y → Y = X l)
    -- EXTRA HYPOTHESIS: the five points are not collinear ("one circle", not a line).
    -- AMBIGUOUS: drop `hnc` and conclude `Cospherical (range X) ∨ Collinear ℝ (range X)`
    -- ("circle or line", the inversive form).
    (hnc : ¬ Collinear ℝ (Set.range X)) :
    Cospherical (Set.range X) := by
  let f := normalizeAt M
  let z : Fin 5 → ℂ := fun i => f (c i).center
  have he : ∀ i j, i ≠ j → f (P i j) = Clifford.secondInter (z i) (z j) :=
    cov_gp_normalize c M P h
  have hz : ∀ i j, i ≠ j → Clifford.secondInter (z i) (z j) ≠ 0 := by
    intro i j hij hh
    have hzero : f M = 0 := by simp [f,normalizeAt]
    exact h.second_ne i j hij (f.injective (((he i j hij).trans hh).trans hzero.symm))
  have hn : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
        Clifford.secondInter (z j) (z k)} := by
    intro i j k hij hik hjk hh
    apply h.noncollinear i j k hij hik hjk
    apply (cov_collinear_affine f).1
    simpa only [Set.image_insert_eq,Set.image_singleton,he i j hij,he i k hik,he j k hjk] using hh
  obtain ⟨Y0,Y1,Y2,Y3,Y4,h0,h1,h2,h3,h4,hY⟩ := Clifford.clifford_two (z 0) (z 1) (z 2) (z 3) (z 4)
    (hz 0 1 (by decide))
    (hz 0 2 (by decide))
    (hz 0 3 (by decide))
    (hz 0 4 (by decide))
    (hz 1 2 (by decide))
    (hz 1 3 (by decide))
    (hz 1 4 (by decide))
    (hz 2 3 (by decide))
    (hz 2 4 (by decide))
    (hz 3 4 (by decide))
    (hn 0 1 2 (by decide) (by decide) (by decide))
    (hn 0 1 3 (by decide) (by decide) (by decide))
    (hn 0 1 4 (by decide) (by decide) (by decide))
    (hn 0 2 3 (by decide) (by decide) (by decide))
    (hn 0 2 4 (by decide) (by decide) (by decide))
    (hn 0 3 4 (by decide) (by decide) (by decide))
    (hn 1 2 3 (by decide) (by decide) (by decide))
    (hn 1 2 4 (by decide) (by decide) (by decide))
    (hn 1 3 4 (by decide) (by decide) (by decide))
    (hn 2 3 4 (by decide) (by decide) (by decide))
  have eq0 : Y0 = f (X 0) := by
    have hh := cov_gamma_of_four (z := z) 1 2 3 4 hn
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h0.1 h0.2.1 h0.2.2.1 h0.2.2.2
    have hall : OnAllGamma P (Finset.univ.erase 0) (f.symm Y0) := by
      intro i hi j hj k hk hij hik hjk
      apply (cov_cospherical_affine f).1
      simp only [Set.image_insert_eq,Set.image_singleton,f.apply_symm_apply,he i j hij,he i k hik,he j k hjk]
      have hs : ∀ q : Fin 5, q ∈ Finset.univ.erase 0 → q ∈ ({1,2,3,4} : Set (Fin 5)) := by
        intro q hq; simp only [Finset.mem_erase,Finset.mem_univ,true_and,and_true,Set.mem_insert_iff,Set.mem_singleton_iff] at hq ⊢; omega
      exact hh i (hs i hi) j (hs j hj) k (hs k hk) hij hik hjk
    have hu := congrArg f (hXu 0 (f.symm Y0) hall)
    simpa only [f.apply_symm_apply] using hu
  have eq1 : Y1 = f (X 1) := by
    have hh := cov_gamma_of_four (z := z) 0 2 3 4 hn
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h1.1 h1.2.1 h1.2.2.1 h1.2.2.2
    have hall : OnAllGamma P (Finset.univ.erase 1) (f.symm Y1) := by
      intro i hi j hj k hk hij hik hjk
      apply (cov_cospherical_affine f).1
      simp only [Set.image_insert_eq,Set.image_singleton,f.apply_symm_apply,he i j hij,he i k hik,he j k hjk]
      have hs : ∀ q : Fin 5, q ∈ Finset.univ.erase 1 → q ∈ ({0,2,3,4} : Set (Fin 5)) := by
        intro q hq; simp only [Finset.mem_erase,Finset.mem_univ,true_and,and_true,Set.mem_insert_iff,Set.mem_singleton_iff] at hq ⊢; omega
      exact hh i (hs i hi) j (hs j hj) k (hs k hk) hij hik hjk
    have hu := congrArg f (hXu 1 (f.symm Y1) hall)
    simpa only [f.apply_symm_apply] using hu
  have eq2 : Y2 = f (X 2) := by
    have hh := cov_gamma_of_four (z := z) 0 1 3 4 hn
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h2.1 h2.2.1 h2.2.2.1 h2.2.2.2
    have hall : OnAllGamma P (Finset.univ.erase 2) (f.symm Y2) := by
      intro i hi j hj k hk hij hik hjk
      apply (cov_cospherical_affine f).1
      simp only [Set.image_insert_eq,Set.image_singleton,f.apply_symm_apply,he i j hij,he i k hik,he j k hjk]
      have hs : ∀ q : Fin 5, q ∈ Finset.univ.erase 2 → q ∈ ({0,1,3,4} : Set (Fin 5)) := by
        intro q hq; simp only [Finset.mem_erase,Finset.mem_univ,true_and,and_true,Set.mem_insert_iff,Set.mem_singleton_iff] at hq ⊢; omega
      exact hh i (hs i hi) j (hs j hj) k (hs k hk) hij hik hjk
    have hu := congrArg f (hXu 2 (f.symm Y2) hall)
    simpa only [f.apply_symm_apply] using hu
  have eq3 : Y3 = f (X 3) := by
    have hh := cov_gamma_of_four (z := z) 0 1 2 4 hn
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h3.1 h3.2.1 h3.2.2.1 h3.2.2.2
    have hall : OnAllGamma P (Finset.univ.erase 3) (f.symm Y3) := by
      intro i hi j hj k hk hij hik hjk
      apply (cov_cospherical_affine f).1
      simp only [Set.image_insert_eq,Set.image_singleton,f.apply_symm_apply,he i j hij,he i k hik,he j k hjk]
      have hs : ∀ q : Fin 5, q ∈ Finset.univ.erase 3 → q ∈ ({0,1,2,4} : Set (Fin 5)) := by
        intro q hq; simp only [Finset.mem_erase,Finset.mem_univ,true_and,and_true,Set.mem_insert_iff,Set.mem_singleton_iff] at hq ⊢; omega
      exact hh i (hs i hi) j (hs j hj) k (hs k hk) hij hik hjk
    have hu := congrArg f (hXu 3 (f.symm Y3) hall)
    simpa only [f.apply_symm_apply] using hu
  have eq4 : Y4 = f (X 4) := by
    have hh := cov_gamma_of_four (z := z) 0 1 2 3 hn
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      h4.1 h4.2.1 h4.2.2.1 h4.2.2.2
    have hall : OnAllGamma P (Finset.univ.erase 4) (f.symm Y4) := by
      intro i hi j hj k hk hij hik hjk
      apply (cov_cospherical_affine f).1
      simp only [Set.image_insert_eq,Set.image_singleton,f.apply_symm_apply,he i j hij,he i k hik,he j k hjk]
      have hs : ∀ q : Fin 5, q ∈ Finset.univ.erase 4 → q ∈ ({0,1,2,3} : Set (Fin 5)) := by
        intro q hq; simp only [Finset.mem_erase,Finset.mem_univ,true_and,and_true,Set.mem_insert_iff,Set.mem_singleton_iff] at hq ⊢; omega
      exact hh i (hs i hi) j (hs j hj) k (hs k hk) hij hik hjk
    have hu := congrArg f (hXu 4 (f.symm Y4) hall)
    simpa only [f.apply_symm_apply] using hu
  have hs : f '' Set.range X = {Y0,Y1,Y2,Y3,Y4} := by
    rw [← Set.range_comp]
    ext p
    simp only [Set.mem_range,Set.mem_insert_iff,Set.mem_singleton_iff,Function.comp_apply]
    constructor
    · rintro ⟨i,rfl⟩; fin_cases i <;> simp [eq0,eq1,eq2,eq3,eq4]
    · rintro (rfl|rfl|rfl|rfl|rfl)
      · exact ⟨0,eq0.symm⟩
      · exact ⟨1,eq1.symm⟩
      · exact ⟨2,eq2.symm⟩
      · exact ⟨3,eq3.symm⟩
      · exact ⟨4,eq4.symm⟩
  rcases hY with hY|hY
  · exact (cov_cospherical_affine f).1 (hs.symm ▸ hY)
  · exact False.elim (hnc ((cov_collinear_affine f).1 (hs.symm ▸ hY)))



noncomputable def normalizeSphere (M : Pt) (C : Sphere Pt) : Sphere ℂ :=
  ⟨normalizeAt M C.center,C.radius⟩
 theorem cov_mem_normalizeSphere (M : Pt) (C : Sphere Pt) (z : ℂ) :
    z ∈ normalizeSphere M C ↔ (normalizeAt M).symm z ∈ C := by
  change dist z (normalizeAt M C.center) = C.radius ↔ dist ((normalizeAt M).symm z) C.center = C.radius
  rw [← (normalizeAt M).dist_map, (normalizeAt M).apply_symm_apply]

theorem cov_D1_c_part (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) 
    (hcanonical_nc0 : ¬ Collinear ℝ ({(Clifford.cliffordPoint (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center)),(Clifford.cliffordPoint (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center)),(Clifford.cliffordPoint (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center))} : Set ℂ))
    (hcanonical_circle0 : normalizeSphere M (C 0) = Clifford.circumcircle (Clifford.cliffordPoint (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center)) (Clifford.cliffordPoint (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center)) (Clifford.cliffordPoint (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center)))
    (hcanonical_nc1 : ¬ Collinear ℝ ({(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center))} : Set ℂ))
    (hcanonical_circle1 : normalizeSphere M (C 1) = Clifford.circumcircle (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center)))
    (hcanonical_nc2 : ¬ Collinear ℝ ({(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center))} : Set ℂ))
    (hcanonical_circle2 : normalizeSphere M (C 2) = Clifford.circumcircle (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center)))
    (hcanonical_nc3 : ¬ Collinear ℝ ({(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 5).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center))} : Set ℂ))
    (hcanonical_circle3 : normalizeSphere M (C 3) = Clifford.circumcircle (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 5).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 4).center) (normalizeAt M (c 5).center)))
    (hcanonical_nc4 : ¬ Collinear ℝ ({(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 5).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center))} : Set ℂ))
    (hcanonical_circle4 : normalizeSphere M (C 4) = Clifford.circumcircle (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 5).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 5).center)))
    (hcanonical_nc5 : ¬ Collinear ℝ ({(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center)),(Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center))} : Set ℂ))
    (hcanonical_circle5 : normalizeSphere M (C 5) = Clifford.circumcircle (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 3).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 2).center) (normalizeAt M (c 4).center)) (Clifford.cliffordPoint (normalizeAt M (c 0).center) (normalizeAt M (c 1).center) (normalizeAt M (c 3).center) (normalizeAt M (c 4).center))) :
    ∃ Y : Pt, ∀ m, Y ∈ C m := by
  let f := normalizeAt M
  let z : Fin 6 → ℂ := fun i => f (c i).center
  have he : ∀ i j, i ≠ j → f (P i j) = Clifford.secondInter (z i) (z j) :=
    cov_gp_normalize c M P h
  have hz : ∀ i j, i ≠ j → Clifford.secondInter (z i) (z j) ≠ 0 := by
    intro i j hij hh
    have hzero : f M = 0 := by simp [f,normalizeAt]
    exact h.second_ne i j hij (f.injective (((he i j hij).trans hh).trans hzero.symm))
  have hn : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
        Clifford.secondInter (z j) (z k)} := by
    intro i j k hij hik hjk hh
    apply h.noncollinear i j k hij hik hjk
    apply (cov_collinear_affine f).1
    simpa only [Set.image_insert_eq,Set.image_singleton,he i j hij,he i k hik,he j k hjk] using hh
  obtain ⟨Y,h5,h4,h3,h2,h1,h0⟩ := Clifford.clifford_three (z 0) (z 1) (z 2) (z 3) (z 4) (z 5)
    (hz 0 1 (by decide))
    (hz 0 2 (by decide))
    (hz 0 3 (by decide))
    (hz 0 4 (by decide))
    (hz 0 5 (by decide))
    (hz 1 2 (by decide))
    (hz 1 3 (by decide))
    (hz 1 4 (by decide))
    (hz 1 5 (by decide))
    (hz 2 3 (by decide))
    (hz 2 4 (by decide))
    (hz 2 5 (by decide))
    (hz 3 4 (by decide))
    (hz 3 5 (by decide))
    (hz 4 5 (by decide))
    (hn 0 1 2 (by decide) (by decide) (by decide))
    (hn 0 1 3 (by decide) (by decide) (by decide))
    (hn 0 1 4 (by decide) (by decide) (by decide))
    (hn 0 1 5 (by decide) (by decide) (by decide))
    (hn 0 2 3 (by decide) (by decide) (by decide))
    (hn 0 2 4 (by decide) (by decide) (by decide))
    (hn 0 2 5 (by decide) (by decide) (by decide))
    (hn 0 3 4 (by decide) (by decide) (by decide))
    (hn 0 3 5 (by decide) (by decide) (by decide))
    (hn 0 4 5 (by decide) (by decide) (by decide))
    (hn 1 2 3 (by decide) (by decide) (by decide))
    (hn 1 2 4 (by decide) (by decide) (by decide))
    (hn 1 2 5 (by decide) (by decide) (by decide))
    (hn 1 3 4 (by decide) (by decide) (by decide))
    (hn 1 3 5 (by decide) (by decide) (by decide))
    (hn 1 4 5 (by decide) (by decide) (by decide))
    (hn 2 3 4 (by decide) (by decide) (by decide))
    (hn 2 3 5 (by decide) (by decide) (by decide))
    (hn 2 4 5 (by decide) (by decide) (by decide))
    (hn 3 4 5 (by decide) (by decide) (by decide))
    hcanonical_nc5 hcanonical_nc4 hcanonical_nc3 hcanonical_nc2 hcanonical_nc1 hcanonical_nc0
  refine ⟨f.symm Y,?_⟩
  intro m
  fin_cases m
  · apply (cov_mem_normalizeSphere M (C 0) Y).1
    rw [hcanonical_circle0]
    exact h0.2
  · apply (cov_mem_normalizeSphere M (C 1) Y).1
    rw [hcanonical_circle1]
    exact h1.2
  · apply (cov_mem_normalizeSphere M (C 2) Y).1
    rw [hcanonical_circle2]
    exact h2.2
  · apply (cov_mem_normalizeSphere M (C 3) Y).1
    rw [hcanonical_circle3]
    exact h3.2
  · apply (cov_mem_normalizeSphere M (C 4) Y).1
    rw [hcanonical_circle4]
    exact h4.2
  · apply (cov_mem_normalizeSphere M (C 5) Y).1
    rw [hcanonical_circle5]
    exact h5.2




/-! ## L15 gap 3: D1(c) — the canonical identifications follow from the writer's hypotheses -/

theorem gap_gamma_of_four6 {z : Fin 6 → ℂ} {Y : ℂ} (a b c d : Fin 6)
    (hn : ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
        Clifford.secondInter (z j) (z k)})
    (hab : a ≠ b) (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d) (hcd : c ≠ d)
    (h1 : Y ∈ Clifford.gam (z a) (z b) (z c))
    (h2 : Y ∈ Clifford.gam (z a) (z b) (z d))
    (h3 : Y ∈ Clifford.gam (z a) (z c) (z d))
    (h4 : Y ∈ Clifford.gam (z b) (z c) (z d)) :
    ∀ i ∈ ({a,b,c,d} : Set (Fin 6)), ∀ j ∈ ({a,b,c,d} : Set (Fin 6)),
      ∀ k ∈ ({a,b,c,d} : Set (Fin 6)), i ≠ j → i ≠ k → j ≠ k →
      Cospherical {Clifford.secondInter (z i) (z j),Clifford.secondInter (z i) (z k),
        Clifford.secondInter (z j) (z k),Y} := by
  have h123 := cov_gam_cospherical (hn a b c hab hac hbc) h1
  have h124 := cov_gam_cospherical (hn a b d hab had hbd) h2
  have h134 := cov_gam_cospherical (hn a c d hac had hcd) h3
  have h234 := cov_gam_cospherical (hn b c d hbc hbd hcd) h4
  have hs : ∀ i j k : Fin 4, i ≠ j → i ≠ k → j ≠ k →
      Cospherical {Clifford.secondInter (z (![a,b,c,d] i)) (z (![a,b,c,d] j)),
        Clifford.secondInter (z (![a,b,c,d] i)) (z (![a,b,c,d] k)),
        Clifford.secondInter (z (![a,b,c,d] j)) (z (![a,b,c,d] k)),Y} := by
    intro i j k hij hik hjk
    fin_cases i <;> fin_cases j <;> fin_cases k <;> simp at hij hik hjk
    all_goals simp only [show (⟨0,by decide⟩ : Fin 4) = 0 from rfl,
      show (⟨1,by decide⟩ : Fin 4) = 1 from rfl,
      show (⟨2,by decide⟩ : Fin 4) = 2 from rfl,
      show (⟨3,by decide⟩ : Fin 4) = 3 from rfl,
      show (![a,b,c,d] (0 : Fin 4)) = a from rfl,
      show (![a,b,c,d] (1 : Fin 4)) = b from rfl,
      show (![a,b,c,d] (2 : Fin 4)) = c from rfl,
      show (![a,b,c,d] (3 : Fin 4)) = d from rfl]
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h123.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h124.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h134.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
    · apply h234.subset; intro p hp; simp only [Set.mem_insert_iff,Set.mem_singleton_iff,
        Clifford.secondInter_symm (z b) (z a), Clifford.secondInter_symm (z c) (z a), Clifford.secondInter_symm (z d) (z a), Clifford.secondInter_symm (z c) (z b), Clifford.secondInter_symm (z d) (z b), Clifford.secondInter_symm (z d) (z c)] at hp ⊢; tauto
  intro i hi j hj k hk hij hik hjk
  have he : ∀ q ∈ ({a,b,c,d} : Set (Fin 6)), ∃ t : Fin 4, ![a,b,c,d] t = q := by
    intro q hq
    simp only [Set.mem_insert_iff,Set.mem_singleton_iff] at hq
    rcases hq with rfl|rfl|rfl|rfl
    · exact ⟨0,rfl⟩
    · exact ⟨1,rfl⟩
    · exact ⟨2,rfl⟩
    · exact ⟨3,rfl⟩
  obtain ⟨i',rfl⟩ := he i hi
  obtain ⟨j',rfl⟩ := he j hj
  obtain ⟨k',rfl⟩ := he k hk
  exact hs i' j' k' (fun hh => hij (hh ▸ rfl)) (fun hh => hik (hh ▸ rfl))
    (fun hh => hjk (hh ▸ rfl))

open Clifford ComplexConjugate in
/-- Five Clifford points lying on a circle `S` and not all collinear: three canonical ones are
non-collinear and `S` is their circumcircle. -/
theorem gap_five_circle (c₁ c₂ c₃ c₄ c₅ : ℂ)
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
    (S : Sphere ℂ) (hS : ∀ Q ∈ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₄} : Set ℂ), Q ∈ S)
    (hnc : ¬ Collinear ℝ ({cliffordPoint c₂ c₃ c₄ c₅, cliffordPoint c₁ c₃ c₄ c₅, cliffordPoint c₁ c₂ c₄ c₅, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₃ c₄} : Set ℂ)) :
    ¬ Collinear ℝ ({cliffordPoint c₁ c₂ c₃ c₄, cliffordPoint c₁ c₂ c₃ c₅, cliffordPoint c₁ c₂ c₄ c₅} : Set ℂ) ∧
    S = circumcircle (cliffordPoint c₁ c₂ c₃ c₄) (cliffordPoint c₁ c₂ c₃ c₅) (cliffordPoint c₁ c₂ c₄ c₅) := by
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
  by_cases hW : WW c₁ (conj c₁) c₂ (conj c₂) c₃ (conj c₃) c₄ (conj c₄) c₅ (conj c₅) = 0
  · exfalso
    have e54 : cliffordPoint c₁ c₂ c₃ c₄ = cliffordPoint c₁ c₂ c₃ c₅ := eq_of_cross N5 N4 (cross54 ..) (by rw [hW, mul_zero])
    have e53 : cliffordPoint c₁ c₂ c₃ c₄ = cliffordPoint c₁ c₂ c₄ c₅ := eq_of_cross N5 N3 (cross53 ..) (by rw [hW, mul_zero])
    have e32 : cliffordPoint c₁ c₂ c₄ c₅ = cliffordPoint c₁ c₃ c₄ c₅ := eq_of_cross N3 N2 (cross32 ..) (by rw [hW, mul_zero])
    have e31 : cliffordPoint c₁ c₂ c₄ c₅ = cliffordPoint c₂ c₃ c₄ c₅ := eq_of_cross N3 N1 (cross31 ..) (by rw [hW, mul_zero])
    apply hnc
    refine (collinear_singleton ℝ (cliffordPoint c₁ c₂ c₃ c₄)).subset ?_
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
  have m5 := hS (cliffordPoint c₁ c₂ c₃ c₄) (by simp)
  have m4 := hS (cliffordPoint c₁ c₂ c₃ c₅) (by simp)
  have m3 := hS (cliffordPoint c₁ c₂ c₄ c₅) (by simp)
  have hai := S.cospherical.affineIndependent_of_mem_of_ne m5 m4 m3 ne54 ne53 ne43
  have hnc3 := affineIndependent_iff_not_collinear_set.1 hai
  refine ⟨hnc3, ?_⟩
  by_contra hne
  rcases eq_of_mem_sphere_of_mem_sphere_of_finrank_eq_two Complex.finrank_real_complex hne ne54
    m5 m4 m3 (mem_circumcircle_left _ _ _) (mem_circumcircle_middle hnc3)
    (mem_circumcircle_right hnc3) with e | e
  · exact ne53 e.symm
  · exact ne43 e.symm

noncomputable abbrev zc (c : Fin 6 → Sphere Pt) (M : Pt) (i : Fin 6) : ℂ := normalizeAt M (c i).center

theorem gap_hz (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) :
    ∀ i j, i ≠ j → Clifford.secondInter (zc c M i) (zc c M j) ≠ 0 := by
  have he := cov_gp_normalize c M P h
  intro i j hij hh
  have hzero : normalizeAt M M = 0 := by simp [normalizeAt]
  exact h.second_ne i j hij ((normalizeAt M).injective (((he i j hij).trans hh).trans hzero.symm))

theorem gap_hn (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) :
    ∀ i j k, i ≠ j → i ≠ k → j ≠ k →
      ¬ Collinear ℝ {Clifford.secondInter (zc c M i) (zc c M j),
        Clifford.secondInter (zc c M i) (zc c M k), Clifford.secondInter (zc c M j) (zc c M k)} := by
  have he := cov_gp_normalize c M P h
  intro i j k hij hik hjk hh
  apply h.noncollinear i j k hij hik hjk
  apply (cov_collinear_affine (normalizeAt M)).1
  simpa only [Set.image_insert_eq,Set.image_singleton,he i j hij,he i k hik,he j k hjk] using hh

/-- The writer's uniquely determined Clifford point is the repository's explicit one. -/
theorem gap_X_eq (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (m l a b c' d : Fin 6) (hml : m ≠ l)
    (hab : a ≠ b) (hac : a ≠ c') (had : a ≠ d) (hbc : b ≠ c') (hbd : b ≠ d) (hcd : c' ≠ d)
    (hset : ∀ q ∈ (Finset.univ.erase m).erase l, q ∈ ({a,b,c',d} : Set (Fin 6))) :
    normalizeAt M (X m l) = Clifford.cliffordPoint (zc c M a) (zc c M b) (zc c M c') (zc c M d) := by
  let f := normalizeAt M
  have he : ∀ i j, i ≠ j → f (P i j) = Clifford.secondInter (zc c M i) (zc c M j) :=
    cov_gp_normalize c M P h
  have hz := gap_hz c M P h
  have hn := gap_hn c M P h
  have hm := Clifford.cliffordPoint_mem_gams (zc c M a) (zc c M b) (zc c M c') (zc c M d)
    (hz a b hab) (hz a c' hac) (hz a d had) (hz b c' hbc) (hz b d hbd) (hz c' d hcd)
    (hn a b c' hab hac hbc) (hn a b d hab had hbd) (hn a c' d hac had hcd) (hn b c' d hbc hbd hcd)
  have hh := gap_gamma_of_four6 (z := zc c M) a b c' d hn hab hac had hbc hbd hcd
    hm.1 hm.2.1 hm.2.2.1 hm.2.2.2
  have hall : OnAllGamma P ((Finset.univ.erase m).erase l)
      (f.symm (Clifford.cliffordPoint (zc c M a) (zc c M b) (zc c M c') (zc c M d))) := by
    intro i hi j hj k hk hij hik hjk
    apply (cov_cospherical_affine f).1
    simp only [Set.image_insert_eq,Set.image_singleton,f.apply_symm_apply,he i j hij,he i k hik,he j k hjk]
    exact hh i (hset i hi) j (hset j hj) k (hset k hk) hij hik hjk
  have hu := congrArg f (hXu m l _ hml hall)
  simpa only [f.apply_symm_apply] using hu.symm

/-- For one `m`: the writer's hypotheses force the repository's canonical non-collinearity and
the identification of (normalised) `C m` with the canonical circumcircle. -/
theorem gap_canon (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l})
    (m s1 s2 s3 s4 s5 : Fin 6) (d12 : s1 ≠ s2) (d13 : s1 ≠ s3) (d14 : s1 ≠ s4) (d15 : s1 ≠ s5) (d23 : s2 ≠ s3) (d24 : s2 ≠ s4) (d25 : s2 ≠ s5) (d34 : s3 ≠ s4) (d35 : s3 ≠ s5) (d45 : s4 ≠ s5) (m1 : s1 ≠ m) (m2 : s2 ≠ m) (m3 : s3 ≠ m) (m4 : s4 ≠ m) (m5 : s5 ≠ m)
    (hcov : ∀ l, l ≠ m → l = s1 ∨ l = s2 ∨ l = s3 ∨ l = s4 ∨ l = s5) :
    ¬ Collinear ℝ ({Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s4), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s4) (zc c M s5)} : Set ℂ) ∧
    normalizeSphere M (C m) = Clifford.circumcircle (Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s4)) (Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s5)) (Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s4) (zc c M s5)) := by
  have hz := gap_hz c M P h
  have hn := gap_hn c M P h
  have x1 : normalizeAt M (X m s1) = Clifford.cliffordPoint (zc c M s2) (zc c M s3) (zc c M s4) (zc c M s5) :=
    gap_X_eq c M P h X hXu m s1 s2 s3 s4 s5 (Ne.symm m1) d23 d24 d25 d34 d35 d45 (by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcov q hq.2 with e | e | e | e | e <;>
        first | exact absurd e hq.1 | (subst e; simp))
  have x2 : normalizeAt M (X m s2) = Clifford.cliffordPoint (zc c M s1) (zc c M s3) (zc c M s4) (zc c M s5) :=
    gap_X_eq c M P h X hXu m s2 s1 s3 s4 s5 (Ne.symm m2) d13 d14 d15 d34 d35 d45 (by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcov q hq.2 with e | e | e | e | e <;>
        first | exact absurd e hq.1 | (subst e; simp))
  have x3 : normalizeAt M (X m s3) = Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s4) (zc c M s5) :=
    gap_X_eq c M P h X hXu m s3 s1 s2 s4 s5 (Ne.symm m3) d12 d14 d15 d24 d25 d45 (by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcov q hq.2 with e | e | e | e | e <;>
        first | exact absurd e hq.1 | (subst e; simp))
  have x4 : normalizeAt M (X m s4) = Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s5) :=
    gap_X_eq c M P h X hXu m s4 s1 s2 s3 s5 (Ne.symm m4) d12 d13 d15 d23 d25 d35 (by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcov q hq.2 with e | e | e | e | e <;>
        first | exact absurd e hq.1 | (subst e; simp))
  have x5 : normalizeAt M (X m s5) = Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s4) :=
    gap_X_eq c M P h X hXu m s5 s1 s2 s3 s4 (Ne.symm m5) d12 d13 d14 d23 d24 d34 (by
      intro q hq
      simp only [Finset.mem_erase, Finset.mem_univ, and_true] at hq
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
      rcases hcov q hq.2 with e | e | e | e | e <;>
        first | exact absurd e hq.1 | (subst e; simp))
  have himg : normalizeAt M '' {p : Pt | ∃ l, l ≠ m ∧ p = X m l} = ({Clifford.cliffordPoint (zc c M s2) (zc c M s3) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s3) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s4)} : Set ℂ) := by
    ext q
    simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨p, ⟨l, hl, rfl⟩, rfl⟩
      rcases hcov l hl with e | e | e | e | e <;> subst e
      · exact Or.inl x1
      · exact Or.inr (Or.inl x2)
      · exact Or.inr (Or.inr (Or.inl x3))
      · exact Or.inr (Or.inr (Or.inr (Or.inl x4)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr x5)))
    · rintro (e | e | e | e | e)
      · exact ⟨X m s1, ⟨s1, m1, rfl⟩, x1.trans e.symm⟩
      · exact ⟨X m s2, ⟨s2, m2, rfl⟩, x2.trans e.symm⟩
      · exact ⟨X m s3, ⟨s3, m3, rfl⟩, x3.trans e.symm⟩
      · exact ⟨X m s4, ⟨s4, m4, rfl⟩, x4.trans e.symm⟩
      · exact ⟨X m s5, ⟨s5, m5, rfl⟩, x5.trans e.symm⟩
  have hnc5 : ¬ Collinear ℝ ({Clifford.cliffordPoint (zc c M s2) (zc c M s3) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s3) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s4)} : Set ℂ) := by
    rw [← himg]; intro hh; exact hCnc m ((cov_collinear_affine (normalizeAt M)).1 hh)
  have hS : ∀ Q ∈ ({Clifford.cliffordPoint (zc c M s2) (zc c M s3) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s3) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s4) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s5), Clifford.cliffordPoint (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s4)} : Set ℂ), Q ∈ normalizeSphere M (C m) := by
    intro Q hQ
    rw [← himg] at hQ
    obtain ⟨p, ⟨l, hl, rfl⟩, rfl⟩ := hQ
    rw [cov_mem_normalizeSphere, (normalizeAt M).symm_apply_apply]
    exact hC m l (Ne.symm hl)
  exact gap_five_circle (zc c M s1) (zc c M s2) (zc c M s3) (zc c M s4) (zc c M s5) (hz s1 s2 d12) (hz s1 s3 d13) (hz s1 s4 d14) (hz s1 s5 d15) (hz s2 s3 d23) (hz s2 s4 d24) (hz s2 s5 d25) (hz s3 s4 d34) (hz s3 s5 d35) (hz s4 s5 d45) (hn s1 s2 s3 d12 d13 d23) (hn s1 s2 s4 d12 d14 d24) (hn s1 s2 s5 d12 d15 d25) (hn s1 s3 s4 d13 d14 d34) (hn s1 s3 s5 d13 d15 d35) (hn s1 s4 s5 d14 d15 d45) (hn s2 s3 s4 d23 d24 d34) (hn s2 s3 s5 d23 d25 d35) (hn s2 s4 s5 d24 d25 d45) (hn s3 s4 s5 d34 d35 d45)
    (normalizeSphere M (C m)) hS hnc5

/-- **D1(c), exact writer statement.** -/
theorem cov_D1_c (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    -- EXTRA HYPOTHESIS: general position — each Clifford point is well defined.
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt)
    (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    -- EXTRA HYPOTHESIS: general position — the five points on `C m` are not collinear, so
    -- `C m` is the unique circle through them (this is the hypothesis under which part (b)
    -- produces a circle).
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) :
    ∃ Y : Pt, ∀ m, Y ∈ C m := by
  obtain ⟨k0, e0⟩ := gap_canon c M P h X hXu C hC hCnc 0 1 2 3 4 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k1, e1⟩ := gap_canon c M P h X hXu C hC hCnc 1 0 2 3 4 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k2, e2⟩ := gap_canon c M P h X hXu C hC hCnc 2 0 1 3 4 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k3, e3⟩ := gap_canon c M P h X hXu C hC hCnc 3 0 1 2 4 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k4, e4⟩ := gap_canon c M P h X hXu C hC hCnc 4 0 1 2 3 5
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  obtain ⟨k5, e5⟩ := gap_canon c M P h X hXu C hC hCnc 5 0 1 2 3 4
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  exact cov_D1_c_part c M P h X hX hXu C hC hCnc k0 e0 k1 e1 k2 e2 k3 e3 k4 e4 k5 e5

theorem cov_D1_c_exact (c : Fin 6 → Sphere Pt) (M : Pt) (P : Fin 6 → Fin 6 → Pt)
    (h : CliffordGP 6 c M P) (X : Fin 6 → Fin 6 → Pt)
    (hX : ∀ m l, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) (X m l))
    (hXu : ∀ m l Y, m ≠ l → OnAllGamma P ((Finset.univ.erase m).erase l) Y → Y = X m l)
    (C : Fin 6 → Sphere Pt) (hC : ∀ m l, m ≠ l → X m l ∈ C m)
    (hCnc : ∀ m, ¬ Collinear ℝ {p : Pt | ∃ l, l ≠ m ∧ p = X m l}) :
    classical_D1_c c M P h X hX hXu C hC hCnc :=
  cov_D1_c c M P h X hX hXu C hC hCnc

end Clifford.Classical
