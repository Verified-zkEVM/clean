# femtoCairo - A minimal ISA with simple AIR verification

femtoCairo is a minimal ISA inspired by the [Cairo ISA](https://eprint.iacr.org/2021/1063), still designed to be able to encode universal computations.

The main design ideas are the following:

- The ISA works natively over any sufficiently large field $\mathbb{F}$. Programs will perform operations and will work natively over $\mathbb{F}$. In practice, we require that $|\mathbb{F}| > 2^{8}$, which covers most of small field proof systems.
- Encoding and decoding of instructions is trivial, and is very cheap.
- We trade-off efficiency for extreme simplicity, the downside is that trivial operations will take multiple instructions.
- The memory is split into two parts: a program memory, and a data memory. Both of those are read-only memories, but the program memory is fixed and publicly known, while the data memory is committed by the prover, and is arbitrary. We furthermore assume that the program is encoded correctly. The whole point of the execution is to perform assertions on the data memory.

## Read-only memory

First, the prover commits to a **data memory function** 
$$
\mathfrak{m} : [0, \text{addr}_{\text{max}}) \to \mathbb{F}
$$
where $\text{addr}_{\text{max}}$ is the maximum address of the memory and is a parameter of the VM. Concretely, we can assume that $\text{addr}_{\text{max}}$ is a power of two. We further assume that 
$$
\text{addr}_{\text{max}} < |\mathbb{F}|
$$
such that all memory is addressable using one field element.

Additionally, the execution can read from a **program memory function**
$$
\mathfrak{p} : [0, \text{pc}_{\text{max}}) \to \mathbb{F}
$$
where $\text{pc}_{\text{max}}$ is the maximum program counter. This function is fixed, publicly known, and **trusted by the verifier**. As before, we assume that
$$
\text{pc}_{\text{max}} < |\mathbb{F}|.
$$

## Instructions encoding
Each instruction in the program is encoded in 4 field elements, and is addressed by the $\text{pc}$ register.
1. $\mathfrak{p}(\text{pc})$ contains the instruction. The first 2 bits are reserved for the instruction type, then the following 6 bits are reserved for the addressing modes of respectively the first, second and third operands (2 bits for each one).
1. $\mathfrak{p}(\text{pc} + 1)$ contains the first operand $\text{op}_1$
1. $\mathfrak{p}(\text{pc} + 2)$ contains the first operand $\text{op}_2$
1. $\mathfrak{p}(\text{pc} + 3)$ contains the third operand $\text{op}_3$


## State transition function

Given a data memory $\mathfrak{m}$ and a program memory $\mathfrak{p}$, the state transition function's purpose is to transition from the current register state to the next register state:
$$
(\text{pc}, \text{ap}, \text{fp}) \rightsquigarrow (\text{pc}', \text{ap}', \text{fp}').
$$
We remark that the whole point of the execution is to **perform assertions on the values of the memory**, following the ISA semantics. By design, the prover can commit to an arbitrary data memory function.

The program starts in the state $(0, 0, 0)$. The transition function is specified in the pseudocode below.

```python
# verifies a state transition function:
# inputs are the memory functions p and m, current state (pc, ap, fp)
# and claimed next state (pc_next, ap_next, fp_next)

# decoding of the instruction: 4 elements of 2 bits each
instruction_type, addressing1, addressing2, addressing3 = decode(p(pc))
op1 = p(pc + 1)
op2 = p(pc + 2)
op3 = p(pc + 3)

if addressing1 == 0:
    v1 = m(m(ap + op1))
else if addressing1 == 1:
    v1 = m(ap + op1)
else if addressing1 == 2:
    v1 = m(fp + op1)
else:
    v1 = op1

if addressing2 == 0:
    v2 = m(m(ap + op2))
else if addressing2 == 1:
    v2 = m(ap + op2)
else if addressing2 == 2:
    v2 = m(fp + op2)
else:
    v2 = op2

if addressing3 == 0:
    v3 = m(m(ap + op3))
else if addressing3 == 1:
    v3 = m(ap + op3)
else if addressing3 == 2:
    v3 = m(fp + op3)
else:
    v3 = op3

if instruction_type == ADD:
    assert v3 == v1 + v2

if instruction_type == MUL:
    assert v3 == v1 * v2

if instruction_type == STORE_STATE:
    assert v1 == pc
    assert v2 == ap
    assert v3 == fp

if instruction_type == LOAD_STATE:
    assert pc_next == v1
    assert ap_next == v2
    assert fp_next == v3
else:
    assert pc_next == pc + 4
```

The addressing modes for each operand can be one of the following:
- **Double indirection**: the operand is an offset from the `ap` register, and the value is read from the memory at the address stored in memory at that address.
- **ap-relative**: the operand is an offset from the `ap` register, and the value is read from the memory at that address.
- **fp-relative**: the operand is an offset from the `fp` register, and the value is read from the memory at that address.
- **Immediate**: the operand is the value itself.

We define accessing the memory out-of-bounds, as well as not encoding correctly the instruction type to be **undefined behaviour** (UB).

As a final remark, technically the only addressing modes strictly needed are the immediate and the double indirection, which would save some constraints.

### Universality of femtoCairo
The instructions `ADD`, `MUL`, `STORE_STATE` and `LOAD_STATE` are enough to encode any useful program. We give some examples of gadgets that can be implemented using these instructions. We refer to the Cairo paper for more details on how to structure the memory to encode loops and recursion, but we note that our ISA can encode Cairo's instructions such as `RET`, `CALL` and so on. In our assembly, we write `[[ap + off]]` to denote double indirection, `[ap + off]` to denote ap-relative access, and `[fp + off]` to denote fp-relative access, and `imm` to denote an immediate value.
We give now some examples of gadgets that can be implemented using these instructions. We use the same Cairo convention that `ap` points to the first unused memory cell. For simplicity, we do not show the advancement of `ap` for every complex instruction, but we note that advancing `ap` can trivially be achieved in this ISA.

Assert that a memory cell `dst` is a constant `value`.
```python
add dst 0 value
```

Cairo's `jump abs <dst>`.
```python
store_state [ap + 0] [ap + 1] [ap + 2]
load_state dst [ap + 1] [ap + 2]
```

Cairo's `jump rel <off>`, which is a jump to `pc + off`
```python
store_state [ap + 0] [ap + 1] [ap + 2]
add [ap + 0] off [ap + 3]      # compute pc + off
load_state [ap + 3] [ap + 1] [ap + 2]
```

Cairo's `jump rel <off> if [fp + 5] != 0`, which is more tricky, as we need to conditionally jump.
```python
# first, load the condition value into [ap + 0]
add [fp + 5] 0 [ap + 0]

# check if the value is zero, we take inspiration from the IsZero gadget
# the prover witnesses the inverse of the value in [ap + 1], or 0 if the value is 0
# in Cairo, this would be achieved using "prover hints" (sec 2.5.1)

# compute out == -value * inv + 1
mul [ap + 0] -1 [ap + 2]    # -value
mul [ap + 2] [ap + 1] [ap + 3]  # -value * inv
add [ap + 3] 1 [ap + 4]     # out = -value * inv + 1

# assert that out * value == 0
mul [ap + 4] [ap + 0] 0

# now, in [ap + 4] we have 1 if we want to jump, and 0 otherwise

# compute if we do not jump
mul [ap + 4] -1 [ap + 5]
add [ap + 5] 1 [ap + 6]      # [ap + 6] = 1 - out

# load current state into [ap + 7] [ap + 8] [ap + 9]
store_state [ap + 7] [ap + 8] [ap + 9]

# compute the next pc if we do jump
add [ap + 7] off [ap + 10]   # if jump, pc + off

# select the next pc
mul [ap + 6] [ap + 7] [ap + 11]   # if not jump, pc
mul [ap + 4] [ap + 10] [ap + 12]   # if jump, dst
add [ap + 11] [ap + 12] [ap + 13] # [ap + 13] = next pc

# jump to the next pc
load_state [ap + 13] [ap + 8] [ap + 9]
```

It is easy to see that we can implement any Cairo instruction using those gadgets, at the cost of encoding complex semantics in more instructions. Since we can implement a VM for Cairo in femtoCairo, it follows that femtoCairo is at least as computationally powerful as Cairo.

## AIR constraints for the state transition function

We express the state transition function as a set of algebraic constraints. We assume that we have an AIR trace, where each row corresponds to a step in the execution. We also assume that we can invoke lookup arguments in the program memory and in the data memory.

```python
# let pc, ap, fp be the registers in the current row,
# and pc_next, ap_next, fp_next be the registers in the next row

# decode the instruction
instruction = lookup_p(pc)
op1 = lookup_p(pc + 1)
op2 = lookup_p(pc + 2)
op3 = lookup_p(pc + 3)

bits = num2bits(instruction, 8)

# read into memory
v1 = (1 - bits[2]) * (1 - bits[3]) * lookup_m(lookup_m(ap + op1)) +
     bits[2]       * (1 - bits[3]) * lookup_m(ap + op1) +
     (1 - bits[2]) * bits[3]       * lookup_m(fp + op1) +
     bits[2]       * bits[3]       * op1

v2 = (1 - bits[4]) * (1 - bits[5]) * lookup_m(lookup_m(ap + op2)) +
     bits[4]       * (1 - bits[5]) * lookup_m(ap + op2) +
     (1 - bits[4]) * bits[5]       * lookup_m(fp + op2) +
     bits[4]       * bits[5]       * op2

v3 = (1 - bits[6]) * (1 - bits[7]) * lookup_m(lookup_m(ap + op3)) +
     bits[6]       * (1 - bits[7]) * lookup_m(ap + op3) +
     (1 - bits[6]) * bits[7]       * lookup_m(fp + op3) +
     bits[6]       * bits[7]       * op3

# enforce the transition semantics
is_add = (1 - bits[0]) * (1 - bits[1])
is_mul = bits[0] * (1 - bits[1])
is_store_state = (1 - bits[0]) * bits[1]
is_load_state = bits[0] * bits[1]

assert is_add * (v3 - (v1 + v2)) == 0
assert is_mul * (v3 - (v1 * v2)) == 0

assert is_store_state * (v1 - pc) == 0
assert is_store_state * (v2 - ap) == 0
assert is_store_state * (v3 - fp) == 0

assert is_load_state * (pc_next - v1) == 0
assert is_load_state * (ap_next - v2) == 0
assert is_load_state * (fp_next - v3) == 0

assert (1 - is_load_state) * (pc_next - (pc + 4)) == 0
assert (1 - is_load_state) * (ap_next - ap) == 0
assert (1 - is_load_state) * (fp_next - fp) == 0
```