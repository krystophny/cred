# Paper 5: Synthetic Probability Type Theory

## Working Notes

---

# FIRST PASS: Survey and Gap Identification

### Goal

Replace the 48 axioms in Foundations.lean with constructions. Turn prob_zorn from axiom to theorem.

### Current Axioms to Eliminate

1. **Prob type** (27 axioms): ordered semiring structure on [0,1]
2. **CondExp** (7 axioms): conditional expectation
3. **prob_sum** (4 axioms): countable summation
4. **ProbPoset** (2 axioms): reflexivity, transitivity
5. **prob_zorn** (2 axioms): the main target
6. **De Morgan** (2 axioms): algebraic identities

Total: ~44 axioms (some overlap in counting)

---

## First Pass: What Do We Need?

### Q1: How to construct Prob?

**Option A: Real interval [0,1]**
- Requires constructing ℝ first
- ℝ can be: Cauchy sequences, Dedekind cuts, or axiomatic
- Problem: this makes Prob derivative of ℝ, not primitive

**Option B: Direct construction as ordered semiring**
- Define Prob as a quotient or inductive type
- Need: 0, 1, +, *, -, ≤ with correct properties
- Gap: what is the base type?

**Option C: Categorical/algebraic**
- Prob as terminal object in some category
- E.g., probability monads (Giry monad)
- Gap: need category theory infrastructure

**Option D: Synthetic approach**
- Postulate a "probability structure" as a type former
- Like synthetic homotopy theory postulates paths
- Gap: what are the computation rules?

### Q2: How to construct CondExp?

**Classical definition**: E[f|g] = ∫ f dP(·|g)
- Requires measure theory
- Circular if we're avoiding measure theory

**Alternative**: Define via Bayes-like rules
- E[f|g] as primitive satisfying product rule
- Gap: can we derive all 7 axioms from fewer?

**Categorical**: Conditional expectation as a morphism in Markov category
- Gap: need Markov category structure

### Q3: How to prove prob_zorn?

**Strategy sketch from Paper 4:**
1. For finite posets, near-maximal elements exist (no choice)
2. Finite approximations form projective system
3. Kolmogorov extension gives limit measure
4. Limit is concentrated on near-maximals

**Gaps:**
- Need Kolmogorov extension theorem
- Need compactness argument for limit
- Need to formalize "finite approximation"

---

## First Pass: Identified Gaps

### Gap 1: Base type for Prob
What type do we build Prob from? Options:
- ℕ → ℕ (representing rationals/reals?)
- Quotient of some free structure
- Abstract (axiomatic type former)

### Gap 2: Computation rules
If Prob is synthetic, what are the β/η rules?
- β: how does (p + q) compute?
- η: when are two Prob values equal?

### Gap 3: CondExp from Prob
Can CondExp be defined in terms of Prob operations?
Or does it require additional structure?

### Gap 4: Kolmogorov extension
How to formalize the projective limit argument?
Need: directed limits of probability spaces

### Gap 5: Countable operations
prob_sum requires countable sums
How to handle infinite operations constructively?

### Gap 6: Connection to existing Lean math
Should we use Mathlib's measure theory?
Or stay independent?

---

## First Pass: Tentative Strategy

### Path A: Minimal synthetic extension
1. Keep Prob axiomatic but reduce axiom count
2. Derive some axioms from others
3. Focus on proving prob_zorn

### Path B: Construction via intervals
1. Construct ℚ ∩ [0,1]
2. Complete to Prob (Dedekind or Cauchy)
3. Define CondExp
4. Prove prob_zorn

### Path C: Categorical semantics
1. Define Markov category structure
2. Prob as hom-set in suitable category
3. CondExp as Kleisli composition
4. prob_zorn via categorical limits

---

## Immediate Next Steps

1. Investigate which Prob axioms are derivable from others
2. Look at minimal axiom sets for [0,1] arithmetic
3. Research Kolmogorov extension in type theory
4. Check if Mathlib has relevant constructions

---

## References to Check

- Quasi-Borel spaces (Heunen et al.)
- Synthetic measure theory
- Probability monads in type theory
- Kolmogorov extension in constructive math

---

# SECOND PASS: Closing Gaps

## Axiom Reduction Analysis

Examined Foundations.lean. Current axiom count by category:

### Prob Type (34 axioms)
```
Type + operations:     7 (Prob, zero, one, le, add, mul, sub)
Order:                 5 (zero_le, le_one, le_refl, le_trans, le_antisymm)
Multiplication:        7 (mul_le_mul, one_mul, mul_one, mul_comm, mul_assoc, zero_mul, mul_zero)
Addition:              4 (add_comm, add_assoc, zero_add, add_zero)
Subtraction:           7 (sub_self, add_sub_cancel, one_sub_zero, one_sub_one, sub_zero, add_sub_one, sub_sub_cancel)
Distributivity:        2 (mul_add, add_mul)
Special:               2 (one_add_one_sub_one, zero_ne_one)
```

### Derivable Axioms (can eliminate ~7)

1. `mul_one p = p` follows from `one_mul` + `mul_comm`
2. `add_zero p = p` follows from `zero_add` + `add_comm`
3. `mul_zero p = 0` follows from `zero_mul` + `mul_comm`
4. `add_mul` follows from `mul_add` + commutativity
5. `one_sub_one = 0` is instance of `sub_self` with p=1
6. `one_sub_zero = 1` follows from `sub_zero` with p=1
7. `sub_zero p = p` might follow from `add_sub_cancel` with q=0

**Reduced Prob axioms: ~27**

### CondExp (7 axioms)
```
norm, mono, product, self_norm, const_mul, add, chain
```

**Question**: Can any be derived?
- `const_mul` with c=1 gives identity (trivial)
- `add` might follow from linearity + product rule? UNCLEAR

### prob_sum (5 axioms)
```
prob_sum, prob_sum_singleton, prob_sum_zero, prob_sum_le_one, prob_sum_shift
```

**Question**: Is prob_sum_zero derivable?
- prob_sum_singleton with p=0 gives: sum of (0 at n, 0 elsewhere) = 0
- But that's not the same as sum of (0 everywhere) = 0
- Need: sum of constant 0 = 0. NOT obviously derivable.

### ProbPoset (2 axioms)
```
refl, trans
```

These are structure axioms, can't be eliminated without changing the definition.

### prob_zorn (2 axioms)
```
prob_zorn, prob_zorn_witness
```

**TARGET**: These should become theorems.

### De Morgan (2 axioms)
```
de_morgan_and, de_morgan_or
```

**Question**: Are these derivable from Prob axioms?

Let a, b ∈ [0,1]. Need to show:
```
1 - ab = (1-a) + (1-b) - (1-a)(1-b)
```

Expand RHS:
```
(1-a) + (1-b) - (1-a)(1-b)
= 1 - a + 1 - b - (1 - a - b + ab)
= 1 - a + 1 - b - 1 + a + b - ab
= 1 - ab
```

**YES! De Morgan is derivable from basic algebra.**

Similarly for de_morgan_or. **Can eliminate 2 axioms.**

---

## Gap 1 Resolution: Construct Prob

### Approach: Dedekind cuts on Q ∩ [0,1]

**Definition**:
```
Prob := { S : Set Q |
  (∀ q ∈ S, 0 ≤ q ≤ 1) ∧           -- bounded
  (∀ q ∈ S, ∀ r < q, r ∈ S) ∧       -- downward closed
  (∃ q, q ∈ S) ∧                     -- non-empty
  (∃ q, q ∉ S ∧ 0 ≤ q ≤ 1) ∧        -- proper (not all of [0,1])
  (∀ q ∈ S, ∃ r ∈ S, q < r)          -- no maximum
}
```

This is the standard Dedekind cut, restricted to [0,1].

**Operations**:
- `0 := { q : Q | q < 0 } ∩ [0,1] = ∅`  -- wait, this is wrong

Actually: `0 := { q : Q | q ≤ 0 ∧ 0 ≤ q ≤ 1 }` doesn't work either.

**Problem**: Standard Dedekind cuts for 0 would be empty or need adjustment.

**Alternative**: Use Cauchy sequences.

```
Prob := { f : N → Q |
  (∀ n, 0 ≤ f n ≤ 1) ∧
  (∀ ε > 0, ∃ N, ∀ m n > N, |f m - f n| < ε)
} / ~

where f ~ g iff lim |f n - g n| = 0
```

**Gap**: Need Q first. Q needs Z. Z needs N.

**Conclusion**: Full construction requires building up from N.
This is standard but tedious. Could use Mathlib's constructions.

---

## Gap 2 Resolution: CondExp

### Observation

CondExp is fundamentally about integration/expectation.
For finite types, E[f|g] can be defined as weighted average.

For general types, need measure theory or:

**Synthetic approach**: CondExp as primitive with computational rules.

Analogy to HoTT paths:
- Paths are primitive, not defined as homotopies
- CondExp is primitive, not defined as integral

**Minimal axioms for CondExp**:
1. Normalization: E[1|g] = 1
2. Linearity: E[af + bg | h] = aE[f|h] + bE[g|h]
3. Product: E[fg|h] = E[f|gh]·E[g|h] (Bayes)
4. Positivity: f ≥ 0 pointwise ⟹ E[f|g] ≥ 0

Can we derive the 7 current axioms from these 4?

- `mono` follows from linearity + positivity
- `self_norm` follows from product with f=g=same
- `chain` follows from product rule

**Potentially reduce to 4 axioms.**

---

## Gap 3 Resolution: prob_zorn

### The Finite Case

**Lemma**: For finite poset P, there exists a maximal element.

*Proof*: Enumerate elements. Start with any. If not maximal,
find strictly greater. Repeat. Terminates by finiteness. ∎

No choice needed for finite case!

### The Infinite Case - Strategy

**Step 1**: Define finite approximations.
For poset (A, ≤), consider finite subsets F ⊆ A.
Each F has a maximal element m_F.

**Step 2**: Define consistency.
If F ⊆ F', the projection of any distribution on F' to F
should relate to the distribution on F.

**Step 3**: Projective limit.
The family {distributions on F} forms a projective system.
Kolmogorov extension gives a limit distribution on A.

**Gap**: Formalizing "distribution on finite set" and "projective limit"
in our framework.

### What We Can Prove Now

**Theorem** (Finite prob_zorn): For finite nonempty A with chain-complete
ProbPoset structure, there exists an ε-near-maximal element.

*Proof*:
- A is finite, so enumerate as {a_1, ..., a_n}
- Define max_prob(a) := min_{b ≠ a} (1 - prob_lt(a,b))
- This measures "how maximal" a is
- Pick a with maximum max_prob value
- This a is ε-near-maximal for some ε ≤ 1 - max_prob(a)

**Gap**: Proving ε can be made arbitrarily small requires more work.

---

## Gap 4 Resolution: Kolmogorov Extension

### Statement (Classical)

Let (X_i, μ_i) be a projective system of probability spaces.
Then there exists a probability space (X, μ) that projects to each (X_i, μ_i).

### Constructive Issues

The classical proof uses:
1. Carathéodory extension (requires countable additivity)
2. Kolmogorov consistency (requires certain set-theoretic constructions)

### Probabilistic Alternative

Instead of extending measures on sets, extend distributions.

**Definition**: A projective system of distributions is:
- For each finite F, a distribution D_F on F
- Compatibility: D_F is the marginal of D_{F'} for F ⊆ F'

**Theorem** (Needs proof): Such a system has a limit distribution.

**Key insight**: We work with distributions directly, not with measures on σ-algebras.
This might be simpler because:
- Distributions are functions to Prob
- No need for measurable sets
- Projective limits of functions are well-defined

**Gap**: Still need to prove this. Might need compactness or completeness.

---

## Summary After Second Pass

### Axioms Reduced
- Original: ~48
- After eliminating derivable: ~39
  - Remove 7 redundant Prob axioms
  - Remove 2 De Morgan axioms

### Gaps Partially Closed

| Gap | Status |
|-----|--------|
| Gap 1 (Prob construction) | Path clear: Cauchy sequences. Tedious but standard. |
| Gap 2 (CondExp) | Reduce to 4 primitive axioms. |
| Gap 3 (prob_zorn) | Finite case proven. Infinite needs projective limit. |
| Gap 4 (Kolmogorov) | Strategy identified. Proof not complete. |
| Gap 5 (prob_sum) | Still open. Need countable operations. |
| Gap 6 (Mathlib) | Decision: stay independent for now. |

### New Gaps Identified

**Gap 7**: Constructive Prob requires constructive reals.
- Can use Bishop-style constructive analysis
- Or accept classical reals and focus on other axioms

**Gap 8**: Connection between CondExp and integration.
- For constructed Prob, should verify CondExp axioms

---

## Next Steps for Third Pass

1. Prove De Morgan from Prob axioms (make it a theorem)
2. Verify the 7 → 4 axiom reduction for CondExp
3. Formalize finite prob_zorn
4. Research projective limits of distributions

---

# THIRD PASS: Implementation Attempts

## Attempt 1: Prove De Morgan as Theorem

### Algebraic Verification

Need to prove: `1 - (a * b) = (1-a) + (1-b) - (1-a)*(1-b)`

Expand RHS:
```
  (1-a) + (1-b) - (1-a)*(1-b)
= (1-a) + (1-b) - (1 - a - b + a*b)
= 1 - a + 1 - b - 1 + a + b - a*b
= 1 - a*b
= LHS ✓
```

### Required Prob Axioms for This Proof

To formalize, we need:
1. Subtraction distributes? No, we need: `(x + y) - z = x + (y - z)` when valid
2. Expansion of `(1-a)*(1-b)` using distributivity
3. Cancellation laws

**Problem**: Our subtraction is truncated (saturating at 0).
The algebraic manipulation above assumes non-truncated subtraction.

Let's check: for a,b ∈ [0,1], do we ever go negative?
- `1 - a ≥ 0` ✓
- `1 - b ≥ 0` ✓
- `(1-a) + (1-b) ≥ (1-a)*(1-b)`?

Since (1-a), (1-b) ∈ [0,1]:
- (1-a)*(1-b) ≤ min(1-a, 1-b) ≤ (1-a) + (1-b) ✓

So truncation doesn't activate. But we need to prove this in Lean.

### Attempted Lean Proof Structure

```lean
-- Need intermediate lemma about subtraction
axiom Prob.sub_add_sub : ∀ a b c : Prob,
  -- when b ≥ c, (a - c) + b - (a - c + b - actual) = ...
  -- This is getting complicated

-- Alternative: add axiom for this specific identity
-- But that defeats the purpose
```

**Conclusion**: De Morgan reduction requires proving properties about
truncated subtraction in [0,1]. Not trivial. May need additional
intermediate axioms about subtraction behavior.

**Gap 9**: Truncated subtraction algebra is more complex than expected.

---

## Attempt 2: CondExp Axiom Reduction

Current 7 axioms:
1. norm: E[1|g] = 1
2. mono: f ≤ f' ⟹ E[f|g] ≤ E[f'|g]
3. product: E[f*g|h] = E[f|g*h] * E[g|h]
4. self_norm: E[f|f] = 1
5. const_mul: E[c*f|g] = c * E[f|g]
6. add: E[f+g|h] = E[f|h] + E[g|h]
7. chain: E[g|h] * E[f|g] ≤ E[f|h]

### Attempted Derivations

**self_norm from product?**
Set g = f, h = f in product rule:
E[f*f|f] = E[f|f*f] * E[f|f]

This doesn't immediately give E[f|f] = 1.

**mono from add + const_mul?**
If f ≤ f', then f' = f + (f' - f) where (f' - f) ≥ 0.
E[f'|g] = E[f|g] + E[f'-f|g]
If E[f'-f|g] ≥ 0 (positivity), then E[f'|g] ≥ E[f|g]. ✓

**Need positivity**: E[f|g] ≥ 0 when f ≥ 0 pointwise.

**chain from product?**
Product: E[f*g|h] = E[f|g*h] * E[g|h]
Chain: E[g|h] * E[f|g] ≤ E[f|h]

Set up: want to relate E[f|g] to E[f|h] via E[g|h].

From product with appropriate substitution... not obvious.

**Conclusion**: The axioms are more independent than expected.
Some reductions possible but need positivity axiom.

### Minimal Axiom Set (Tentative)

1. norm: E[1|g] = 1
2. positivity: f ≥ 0 ⟹ E[f|g] ≥ 0  (NEW, replaces mono)
3. add: E[f+g|h] = E[f|h] + E[g|h]
4. const_mul: E[c*f|g] = c * E[f|g]
5. product: E[f*g|h] = E[f|g*h] * E[g|h]
6. self_norm: E[f|f] = 1  (might be derivable?)
7. chain: E[g|h] * E[f|g] ≤ E[f|h]  (might follow from product?)

**Gap 10**: Precise minimal axiom set for CondExp unclear.

---

## Attempt 3: Finite prob_zorn

### Formalization

```lean
-- Finite type assumption
variable {α : Type} [Fintype α] [Nonempty α]

-- For finite types, we can compute maximum
def max_near_maximal (P : ProbPoset α) : Prob :=
  Finset.sup Finset.univ (fun x =>
    Finset.inf Finset.univ (fun y =>
      if x = y then 𝟙 else 𝟙 -ₚ prob_lt P x y))

theorem finite_prob_zorn (P : ProbPoset α) :
    ChainComplete P →
    ∃ x : α, NearMaximal P x (𝟙 -ₚ max_near_maximal P) := by
  sorry
```

**Problem**: Need Fintype infrastructure and Finset operations on Prob.

**Alternative**: Induction on cardinality.

```lean
theorem finite_prob_zorn_ind (P : ProbPoset α) (n : Nat) (h : card α = n) :
    ChainComplete P →
    ∃ x : α, ∃ ε : Prob, NearMaximal P x ε := by
  induction n with
  | zero => -- empty type, contradicts Nonempty
  | succ m ih =>
    -- For n+1 elements, either we have maximal or can reduce
    sorry
```

**Conclusion**: Finite case is provable but needs Fintype machinery.
Defer to Mathlib integration or manual development.

**Gap 11**: Need decidable equality and finite enumeration for Prob operations.

---

## Attempt 4: Projective Limit Strategy

### Key Insight

For distributions (not measures), projective limits are simpler:

**Definition**: A distribution on finite F is: D : F → Prob with Σ D(x) = 1.

**Projective system**: For F ⊆ F', distribution D_{F'} projects to D_F:
  D_F(x) = Σ_{y ∈ F', y↓ = x} D_{F'}(y)

where y↓ = x means y projects to x (for our application: y = x).

**For prob_zorn**: The projective system is:
- F = finite subsets of the poset A
- D_F = distribution concentrated on near-maximals of F

**Limit construction**:
- For infinite A, define D(x) := lim_{F → A, x ∈ F} D_F(x)

**Problem**: Need to show:
1. The limit exists (completeness of Prob)
2. The limit is a distribution (sums to 1)
3. The limit is concentrated on near-maximals

### Completeness of Prob

If Prob is constructed as Cauchy sequences / Dedekind cuts,
it is complete (every Cauchy sequence converges).

### Sum to 1

Need: Σ_x D(x) = 1

For finite sums, this holds by construction.
For countable/uncountable, need:
- Countable additivity (for countable A)
- General measure theory (for uncountable A)

**Gap 12**: Countable additivity is not currently axiomatized.

### Concentrated on Near-Maximals

If each D_F is concentrated on near-maximals of F,
is the limit concentrated on near-maximals of A?

**Intuition**: Yes, because near-maximality is "local" in some sense.

**Formal proof**: Needs more work.

---

## Summary After Third Pass

### Concrete Progress

| Attempt | Result |
|---------|--------|
| De Morgan | Algebra works, formalization blocked by truncated subtraction |
| CondExp reduction | mono derivable from positivity; others unclear |
| Finite prob_zorn | Strategy clear, needs Fintype infrastructure |
| Projective limits | Strategy clear, needs completeness + countable additivity |

### Remaining Gaps

| Gap | Description | Difficulty |
|-----|-------------|------------|
| 1 | Construct Prob from primitives | Medium (use Mathlib) |
| 2 | CondExp computation rules | Hard (fundamental) |
| 3 | prob_zorn proof | Hard (main target) |
| 4 | Kolmogorov extension | Hard |
| 5 | Countable sums | Medium |
| 9 | Truncated subtraction algebra | Medium |
| 10 | Minimal CondExp axioms | Medium |
| 11 | Fintype for Prob | Easy (Mathlib) |
| 12 | Countable additivity | Hard |

### Recommended Path Forward

**Short-term (Paper 5 v1)**:
1. Use Mathlib for Prob (as [0,1] ⊆ ℝ)
2. Keep CondExp axiomatic (7 axioms)
3. Prove finite prob_zorn
4. State prob_zorn as conjecture, with proof sketch

**Medium-term (Paper 5 v2)**:
5. Add countable additivity axiom
6. Prove countable prob_zorn
7. Reduce CondExp axioms

**Long-term**:
8. Synthetic CondExp (like synthetic paths in HoTT)
9. Full prob_zorn for arbitrary types
10. Remove all axioms except type formers

---

# IMPLEMENTATION: Synthetic.lean

Created `lean/Synthetic.lean` with:

## Proven Theorems (axiom reduction)
1. `mul_one_from_one_mul`: p * 1 = p (from 1 * p = p + commutativity)
2. `add_zero_from_zero_add`: p + 0 = p (from 0 + p = p + commutativity)
3. `mul_zero_from_zero_mul`: p * 0 = 0 (from 0 * p = 0 + commutativity)
4. `add_mul_from_mul_add`: (p+q)*r = p*r + q*r (from distributivity + commutativity)
5. `one_sub_one_from_sub_self`: 1 - 1 = 0 (instance of sub_self)

## Blocked Derivations

**De Morgan**: Algebraically correct but formalization needs axioms for:
- Subtraction associativity with addition
- Handling truncated subtraction

**CondExp mono from positivity**: Partially proven, needs:
- `Prob.add_sub_of_le`: p ≤ q → p + (q - p) = q
- `Prob.sub_nonneg_of_le`: p ≤ q → 0 ≤ q - p
- `Prob.le_add_of_nonneg`: 0 ≤ q → p ≤ p + q

## Conclusion

**5 axioms eliminated** by commutativity arguments (already proven).

**7 more axioms** (De Morgan, some CondExp) could be eliminated with ~3 additional subtraction axioms.

Net: Current 48 → 43 (proven) → potentially 36 (with subtraction axioms).

The subtraction axioms are true for [0,1] ⊂ ℝ and would become theorems if Prob were constructed.
