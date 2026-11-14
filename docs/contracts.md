# Library contracts

A *contract* states a cost bound for a function whose code is not analysed: a C library
function (`memcpy`), a vendor HAL, a DSP library routine, or a C++ standard algorithm whose
implementation is not wanted in the analysis. Contracts are **trusted**: every use is listed
in the report's `assumptions`, and in certificates a contract is an entry without a body
(`"contract": true`), printed `ASSUMED` by `crosscheck-check`; the program's verdict holds
relative to the contracts (Lean `program_sound`, paper `thm:program-soundness`).

There are two ways to state one:

- `CROSSCHECK_COST(n)` on a declaration: a constant cost `n` (see `clang-plugin/README.md`).
- A **contract file**, given with `--opt=contracts=FILE` (tool) or
  `-fplugin-arg-crosscheck-contracts=FILE` (plugin), for costs that depend on arguments:

```json
{ "format": "crosscheck-contracts", "version": 1,
  "implementation": "newlib 4.3, arm-none-eabi-gcc 13 -O2, Cortex-M4 (example)",
  "contracts": [
    { "function": "memcpy",  "cost": { "c": 8, "per_arg": { "2": 2 } } },
    { "function": "memset",  "cost": { "c": 6, "per_arg": { "2": 1 } } },
    { "function": "arm_fir_q15", "cost": { "c": 40, "per_arg": { "4": 12 } } }
  ] }
```

`cost` is `c + Σ per_arg[i] · max(0, argument i)`, arguments counted from 0, in the units
of the cost model in use (the weights of `clang-plugin/README.md`, "Cost model"; the
default weights are 1). `function` is the qualified name (`std::copy`, `dsp::filter`).

**Use.** At a call, the analysis needs an upper bound of every argument that the cost
depends on (from ranges, requirements, loop invariants or calling contexts); without one
the call is an error. The bound is the contract's cost at those upper bounds. A contract
replaces the function's body if it has one.

**What a contract may not say.** A contract is a bound on *every* execution in the
program's cost units. Amortised or average costs (`std::vector::push_back`, hash maps) and
costs that depend on data rather than on argument sizes are not contracts; their callers
must be rejected or annotated in another way. The C++ standard gives complexity classes,
not constants: the coefficients belong to one implementation and one target, which the
`implementation` field records. Values in the example above are illustrative, not measured.

**Where they come from.** For predictable cores, from the instruction counts of the
compiled routine (or a timing analysis of it, for time units); for complex hardware, a
contract in abstract units is a design budget, not a timing guarantee (Paper II,
"Limitations").
