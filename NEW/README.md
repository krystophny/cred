# CredTT v2: A Fresh Start

## The Deep Questions You Asked

### 1. "Should type theory emerge from credence?"
**Yes.** That's what this folder sketches. Types as credence predicates, not primitive syntax.

### 2. "Are we just doing fuzzy logic with extra steps?"
**Danger is real.** Current CredTT (v1) IS essentially:
- Weighted implications (A ⊢ B @ c)
- NOT true conditioning (P(B|A) = P(A∧B)/P(A))

True conditioning requires DIVISION. De Morgan algebra has no division.

### 3. "Is Agda the right tool?"
**No, but it's useful for exploration.** Agda assumes MLTT. Using it to claim "types emerge" is circular. For genuine foundation:
- Phase 1: Agda sketches (here)
- Phase 2: OCaml implementation (no type theory assumed)
- Phase 3: Self-hosting CredTT in CredTT

## What's In This Folder

```
NEW/
├── MANIFESTO.md       -- Vision: types emerge from credence
├── 01-credence-algebra.md  -- Layer 0: De Morgan algebra
├── 02-judgments.md    -- Layer 1: Γ ⊢ t @ c (no types)
├── 03-types-emerge.md -- Layer 2: Types as predicates Term → C
├── 04-type-formers.md -- Layer 3: Π, Σ, + derived from *, ~, ≤
├── 05-mltt-collapse.md -- Layer 4: Boolean case = MLTT
├── 06-alternatives.md -- Honest assessment of other paths
├── 07-tooling.md      -- Why Agda is problematic
├── sketch.agda        -- Formal sketch (with acknowledged circularity)
└── README.md          -- This file
```

## The Honest Assessment

### What CredTT v1 Actually Is
```
Type theory + credence annotations
= Multi-valued logic on MLTT
= Fuzzy logic in disguise
≠ "Types emerge from credence"
```

### What CredTT v2 Attempts
```
Credence algebra (primitive)
→ Untyped terms with credence judgments
→ Types as credence predicates
→ Type formers from algebra operations
→ MLTT as Boolean collapse
```

### What's Still Missing (For True Conditioning)
```
De Morgan algebra has:  *, ~, ≤
True conditioning needs: / (division)

P(B|A) = P(A∧B) / P(A)  ← Can't express this

Options:
1. Accept we're doing graded logic, not probability
2. Use Markov categories (has conditioning)
3. Use full probability theory (σ-algebras, measures)
```

## The Foundational Options

| Option | What It Is | Pros | Cons |
|--------|-----------|------|------|
| **Stay with De Morgan** | Multi-valued logic | Simple, well-understood | Not true probability |
| **Markov categories** | Categorical probability | True conditioning | Complex |
| **Measure theory** | Probability as foundation | Fully probabilistic | Overkill? |
| **Drop types entirely** | Credence spaces | Radical simplicity | Loses type structure |

## Recommendation

### If You Want True Conditioning
Move to Markov categories or measure theory. De Morgan algebra is insufficient.

### If You Want Graded Logic
Stay with De Morgan but be honest: this is multi-valued logic, not probability. The "conditioning" language is misleading.

### If You Want Types to Emerge
Implement in OCaml, not Agda. Don't assume types at the meta level.

### If You Want a Foundation for All Mathematics
Consider whether types are even the right target. Maybe:
- Credence spaces (no types)
- Categories (types as objects)
- Measure spaces (probabilistic)

## Next Steps

1. **Decide**: Is this graded logic or probability?
2. **Choose algebra**: De Morgan (logic) or Markov (probability)
3. **Implement**: OCaml, not Agda
4. **Be honest**: About what emerges vs what's assumed
