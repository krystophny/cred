# ProbTT Agda Formalization

## Status: Implemented

The ProbTT formalization is complete and type-checks. All modules compile without errors.

## File Structure

```
agda/
  ProbTT/
    Weight.agda           -- De Morgan algebra with BoolDM instance
    Syntax.agda           -- Well-scoped terms and types
    Substitution.agda     -- Parallel substitution with proofs
    Context.agda          -- Well-scoped contexts
    Judgment.agda         -- Weighted typing rules (all formers)
    Properties.agda       -- Metatheorems
    MLTT.agda             -- {0,1} embedding and collapse
    Examples.agda         -- Worked examples
  Everything.agda         -- Module exports
  probtt.agda-lib         -- Library file
```

## What Was Implemented

### Weight.agda
- `DeMorganAlgebra` record with 14 axioms (6 multiplication, 3 complement, 5 order)
- `BoolDM` instance with complete proofs for all axioms
- Derived disjunction: `w ∨ v = ¬(¬w · ¬v)`
- De Morgan laws module

### Syntax.agda
- Well-scoped `Ty n` and `Tm n` using `Fin n` for de Bruijn indices
- All type formers: `⇒` (Π), `×'` (Σ), `+'` (coproduct), `𝟙'`, `𝟘'`, `Id`
- All term formers including `case` for sum elimination and `J` for identity elimination

### Substitution.agda
- Renamings: `Ren m n = Fin m → Fin n`
- Substitutions: `Sub m n = Fin m → Tm n`
- `renTm`, `renTy`: apply renaming
- `substTm`, `substTy`: apply substitution
- `wkTm`, `wkTy`: weakening
- `liftSub`, `singleSub`: substitution operations
- `_[_]`, `_[_]ₜ`: single substitution notation
- `subst-id-tm`, `subst-id-ty`: identity substitution lemmas

### Context.agda
- Well-scoped `Ctx n` with `∅` and `_,_`
- `lookup`: get type at position with appropriate weakening

### Judgment.agda
Parameterized by `DeMorganAlgebra`:

**Type formation** (`_⊢_type`):
- `base-form`, `Π-form`, `Σ-form`, `+-form`, `𝟙-form`, `𝟘-form`, `Id-form`

**Weighted typing** (`_⊢_∶_@_`):
- `t-var`: variables at weight 𝟙
- `t-weaken`: lower weight via order
- `t-lam`, `t-app`: Π intro/elim (app multiplies weights)
- `t-pair`, `t-fst`, `t-snd`: Σ intro/elim (pair multiplies weights)
- `t-inl`, `t-inr`, `t-case`: + intro/elim (case multiplies weights)
- `t-star`: 𝟙 intro at weight 𝟙
- `t-abort`: 𝟘 elim (ex falso)
- `t-refl`, `t-J`: Id intro/elim (J multiplies weights)

**Definitional equality** (`_⊢_≡_∶_@_`):
- `eq-refl`, `eq-sym`, `eq-trans`: equivalence
- `Π-β`, `Σ-β₁`, `Σ-β₂`, `+-β-inl`, `+-β-inr`, `Id-β`: computation rules

### Properties.agda
- `weight-bounded`: all weights ≤ 𝟙
- `id-typed`: identity function at weight 𝟙
- `graded-ex-falso`: from ⊥@w, get anything@w
- `zero-annihilates`: w · 𝟘 = 𝟘
- `preservation-left`: type preservation for definitional equality

### MLTT.agda
- Standard MLTT typing judgment (no weights)
- `embed`: MLTT → ProbTT @ true
- `collapse`: ProbTT @ true → MLTT
- `embed-collapse`: round-trip proof (embed then collapse = id)

### Examples.agda
- Identity function at weight 𝟙
- Application preserves weight through identity
- Pair weight is product
- Ex falso example
- Sum elimination with weight multiplication

## Key Insights

1. **Weights multiply in elimination**: This is the core rule. Application, case, and J all multiply the eliminator weight with the argument weight.

2. **Variables are at weight 𝟙**: This ensures we start with full certainty and only lose it through composition.

3. **MLTT is {0,1} case**: When weights are Boolean, 𝟙·𝟙=𝟙 makes weights invisible.

4. **No addition needed**: De Morgan algebra suffices. Disjunction is derived.

## Build

```bash
cd agda
agda Everything.agda
```

## Dependencies

- Agda 2.6.4+
- agda-stdlib 2.0+
