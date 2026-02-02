# CredTT Agda Formalization

## Status: Implemented

The CredTT formalization is complete and type-checks. All modules compile without errors.

## File Structure

```
agda/
  CredTT/
    Credence.agda         -- De Morgan algebra with BoolDM instance
    Syntax.agda           -- Well-scoped terms and types
    Substitution.agda     -- Parallel substitution with proofs
    Context.agda          -- Well-scoped contexts
    Judgment.agda         -- Credenced typing rules (all formers)
    Properties.agda       -- Metatheorems
    MLTT.agda             -- {0,1} embedding and collapse
    Examples.agda         -- Worked examples
  Everything.agda         -- Module exports
  credtt.agda-lib         -- Library file
```

## What Was Implemented

### Credence.agda
- `DeMorganAlgebra` record with 14 axioms (6 multiplication, 3 complement, 5 order)
- `BoolDM` instance with complete proofs for all axioms
- Derived disjunction: `c1 | c2 = ~(~c1 * ~c2)`
- De Morgan laws module

### Syntax.agda
- Well-scoped `Ty n` and `Tm n` using `Fin n` for de Bruijn indices
- All type formers: `=>` (Pi), `x'` (Sigma), `+'` (coproduct), `1'`, `0'`, `Id`
- All term formers including `case` for sum elimination and `J` for identity elimination

### Substitution.agda
- Renamings: `Ren m n = Fin m -> Fin n`
- Substitutions: `Sub m n = Fin m -> Tm n`
- `renTm`, `renTy`: apply renaming
- `substTm`, `substTy`: apply substitution
- `wkTm`, `wkTy`: weakening
- `liftSub`, `singleSub`: substitution operations
- `_[_]`, `_[_]t`: single substitution notation
- `subst-id-tm`, `subst-id-ty`: identity substitution lemmas

### Context.agda
- Well-scoped `Ctx n` with `empty` and `_,_`
- `lookup`: get type at position with appropriate weakening

### Judgment.agda
Parameterized by `DeMorganAlgebra`:

**Type formation** (`_|-_type`):
- `base-form`, `Pi-form`, `Sigma-form`, `+-form`, `1-form`, `0-form`, `Id-form`

**Credenced typing** (`_|-_:_@_`):
- `t-var`: variables at credence 1
- `t-weaken`: lower credence via order
- `t-lam`, `t-app`: Pi intro/elim (app multiplies credences)
- `t-pair`, `t-fst`, `t-snd`: Sigma intro/elim (pair multiplies credences)
- `t-inl`, `t-inr`, `t-case`: + intro/elim (case multiplies credences)
- `t-star`: 1 intro at credence 1
- `t-abort`: 0 elim (ex falso)
- `t-refl`, `t-J`: Id intro/elim (J multiplies credences)

**Definitional equality** (`_|-_==_:_@_`):
- `eq-refl`, `eq-sym`, `eq-trans`: equivalence
- `Pi-beta`, `Sigma-beta1`, `Sigma-beta2`, `+-beta-inl`, `+-beta-inr`, `Id-beta`: computation rules

### Properties.agda
- `credence-bounded`: all credences <= 1
- `id-typed`: identity function at credence 1
- `graded-ex-falso`: from bot@c, get anything@c
- `zero-annihilates`: c * 0 = 0
- `preservation-left`: type preservation for definitional equality

### MLTT.agda
- Standard MLTT typing judgment (no credences)
- `embed`: MLTT -> CredTT @ true
- `collapse`: CredTT @ true -> MLTT
- `embed-collapse`: round-trip proof (embed then collapse = id)

### Examples.agda
- Identity function at credence 1
- Application preserves credence through identity
- Pair credence is product
- Ex falso example
- Sum elimination with credence multiplication

## Key Insights

1. **Credences multiply in elimination**: This is the core rule. Application, case, and J all multiply the eliminator credence with the argument credence.

2. **Variables are at credence 1**: This ensures we start with full certainty and only lose it through composition.

3. **MLTT is {0,1} case**: When credences are Boolean, 1*1=1 makes credences invisible.

4. **No addition needed**: De Morgan algebra suffices. Disjunction is derived.

## Build

```bash
cd agda
agda Everything.agda
```

## Dependencies

- Agda 2.6.4+
- agda-stdlib 2.0+
