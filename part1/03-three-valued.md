# Three-Valued Collapse: {0, ½, 1}

## The Intermediate Level

Between full graded [0,1] and Boolean {0,1}, there's a useful intermediate:

```
C = {0, ½, 1}

0 = impossible / false
½ = unknown / undecided
1 = certain / true
```

## Operations

### Negation
```
~0 = 1
~½ = ½
~1 = 0
```

### Multiplication (Conjunction)
For closure, we need a convention for ½ * ½:

**Option A: Uncertainty propagates**
```
½ * ½ = ½
```

**Option B: Łukasiewicz-style**
```
½ * ½ = max(0, ½ + ½ - 1) = 0
```

We prefer Option A (uncertainty propagates) as it's more conservative.

Full table (Option A):
```
*  | 0   ½   1
---+-----------
0  | 0   0   0
½  | 0   ½   ½
1  | 0   ½   1
```

### Conditioning
```
(a | 1) = a
(a | 0) = unconstrained (we can set to ½)
(a | ½) determined by chain rule: (a | ½) * ½ = a * ½
```

When a = 1: (1 | ½) * ½ = ½, so (1 | ½) = 1
When a = ½: (½ | ½) * ½ = ½, so (½ | ½) could be 1 or ½
When a = 0: (0 | ½) * ½ = 0, so (0 | ½) = 0

## Connection to Known Logics

### Kleene's Strong K3
```
Values: T, U, F (true, unknown, false)
AND = min
OR = max
NOT: ~T=F, ~U=U, ~F=T
```

K3 has ex falso (F → A = T). We don't.

### Priest's LP (Logic of Paradox)
```
Values: T, B, F (true, both, false)
Designed for paraconsistency
```

LP allows contradictions (value "both"). We have "unknown" instead.

### RM3 (Relevant Mingle, 3-valued)
```
Values: T, U, F
No ex falso
Relevant logic
```

**RM3 is the closest match.** Our three-valued collapse lands here.

## Comparison Table

| Logic | Values | Ex falso? | Our collapse? |
|-------|--------|-----------|---------------|
| Kleene K3 | T, U, F | Yes | No |
| Priest LP | T, B, F | No | No (different interpretation) |
| **RM3** | T, U, F | **No** | **Yes** |
| Łukasiewicz Ł3 | T, U, F | Yes | No |

## What ½ Means

In Cred, ½ represents:

1. **Epistemic uncertainty**: We don't know if true or false
2. **Undecidability**: The proposition is undecidable (Gödel sentences)
3. **Self-reference fixed point**: The liar sentence "This is false" has credence ½
4. **Maximum entropy**: No information either way

## The Collapse Map

```
collapse: [0, 1] → {0, ½, 1}

collapse(c) = 0   if c = 0
collapse(c) = 1   if c = 1
collapse(c) = ½   if 0 < c < 1
```

This is the coarsest collapse that preserves the "unknown" state.

## Why Three Values Are Useful

1. **Simpler than [0,1]**: Only three cases to consider
2. **Richer than Boolean**: Can express "unknown"
3. **Practical**: Many applications need true/false/unknown (databases, AI)
4. **Known territory**: RM3 is well-studied

## The Tower (Updated)

```
[0, 1]          Cred (full graded)
   ↓ collapse (0,1) to ½
{0, ½, 1}       RM3-like (three-valued relevant)
   ↓ collapse ½ to 0 or 1
{0, 1}          Boolean relevant logic
   ↓ add ex falso
Classical       FOL
```
