# Graded Predicates (Not Crisp Sets)

## Classical Sets

A set S is a collection. Membership is binary:
```
x ∈ S  or  x ∉ S
```

Characteristic function:
```
χ_S : X → {0, 1}
χ_S(x) = 1 if x ∈ S, else 0
```

## Graded Predicates

A graded predicate S assigns a credence to each element:
```
S : X → [0, 1]
S(x) = a graded membership/truth value
```

This is like a fuzzy set. In the Cred program we treat gradedness as fundamental; the algebra is primary and interpretation comes later (epistemic vs semantic, etc.).

## Examples

**"Tall people"**
```
Tall : Person → [0, 1]
Tall(Alice) = 0.9   -- Alice is very tall
Tall(Bob) = 0.5     -- Bob is medium height
Tall(Carol) = 0.2   -- Carol is short
```

**"Even numbers"** (crisp)
```
Even : ℕ → [0, 1]
Even(n) = 1 if n mod 2 = 0, else 0
```

Crisp sets are special cases where the predicate only takes values 0 and 1.

## Operations on Graded Predicates

These operations are defined pointwise using the Cred algebra on `[0,1]`. Do not silently read them as classical set-theoretic operations unless you also supply a semantics connecting the predicate values to propositions.

**Algebraic intersection (product t-norm)**
```
(S ∩ T)(x) := S(x) * T(x)
```

**Algebraic union (De Morgan dual)**
```
(S ∪ T)(x) := S(x) + T(x) := ~(~S(x) * ~T(x))
            = S(x) + T(x) - S(x) * T(x)
```

**Complement (NOT)**
```
(~S)(x) := 1 - S(x)
```

**Subset**
```
S ⊆ T  iff  ∀x: S(x) ≤ T(x)
```

## Conditioning on Predicates

Conditioning is not “conditioning a number by a number”. The pointwise values are numbers; conditioning is a primitive constraint relating a joint and an evidence quantity.

If you have:
- an evidence predicate `T : X → [0,1]` (think: `cred(B(x))`)
- a joint predicate `J : X → [0,1]` (think: `cred(A(x) ∧ B(x))`)

then a conditional predicate `K : X → [0,1]` (think: `cred(A(x) | B(x))`) is any function satisfying the chain rule constraint pointwise:
```
K(x) * T(x) = J(x)
```

## The Empty Predicate

```
∅(x) = 0  for all x
```

Everything has zero credence of belonging to ∅.

## The Universal Predicate

```
U(x) = 1  for all x
```

Everything has full credence of belonging to U.

## Comprehension

In Cred, comprehension is unrestricted:
```
{x | φ(x)} is the predicate x ↦ φ(x)
```

For any formula φ assigning credences, we get a predicate.

**Russell's predicate**:
```
R(x) = ~(x(x))   -- "x doesn't belong to itself"
R(R) = ~(R(R))
```

If R(R) = c, then c = 1 - c, so c = 0.5.

Russell's predicate has credence 0.5 of containing itself. Not a paradox, a fixed point.

## Membership Degrees

We can define degree of membership:
```
x ∈_c S  iff  S(x) ≥ c
```

- x ∈_1 S means S(x) = 1 (definite member)
- x ∈_0.5 S means S(x) ≥ 0.5 (more in than out)
- x ∈_0 S means S(x) > 0 (any positive membership)

## Crisp Predicates as Special Case

A predicate S is **crisp** if:
```
∀x: S(x) ∈ {0, 1}
```

Crisp predicates ARE classical sets. They form a subcategory.

## Why Not Just Use Fuzzy Sets?

Fuzzy set theory typically:
1. Uses min/max for AND/OR (not product)
2. Has material implication (ex falso holds)
3. Treats fuzziness as "uncertainty about crisp membership"

Cred:
1. Uses product (probabilistic)
2. Has conditioning (no ex falso)
3. Treats gradedness as fundamental, not epistemic

## The Hierarchy

```
Graded predicates (X → [0, 1])
         ↓ restrict to crisp
Crisp predicates (X → {0, 1})
         ↓ identify with classical sets
Classical sets
```

We work at the top level. Lower levels are special cases.
