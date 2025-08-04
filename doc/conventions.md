# Code Style Conventions

This document outlines the code style conventions used in the Clean project.

## Standard Lean/Mathlib Conventions

We follow the standard Lean and Mathlib conventions for most formatting:

- **Type annotations**: Use spaces around `:` 
  - ✅ `(F : Type)`
  - ❌ `(F:Type)`

- **Assignment operator**: Use spaces around `:=`
  - ✅ `let x := 5`
  - ❌ `let x:=5`

- **General named parameters**: Use spaces around `:=`
  - ✅ `(constant := constant)`
  - ❌ `(constant:=constant)`

For more details, see:
- [Mathlib style guide](https://leanprover-community.github.io/contribute/style.html)
- [Mathlib naming conventions](https://leanprover-community.github.io/contribute/naming.html)

## Local Conventions

### 1. Named Parameters

We omit spaces around `:=` in named parameters:

- ✅ `(F:=F)`, `(α:=α)`, `(constant:=constant)`
- ❌ `(F := F)`, `(α := α)`, `(constant := constant)`

### 2. Polynomial Multiplication

In polynomial expressions, we omit spaces around `*`:

- ✅ `2*a*b`, `a*b + c`, `x*y*z`
- ❌ `2 * a * b`, `a * b + c`, `x * y * z`

### 3. Exponents

Inside exponent expressions, we omit spaces around operators:

- ✅ `2^(8-o)`, `2^(n+1)`, `x^(a*b)`
- ❌ `2^(8 - o)`, `2^(n + 1)`, `x^(a * b)`