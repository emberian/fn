# Countdown and primitive boundary certificates

`Fn2.ACL2.Countdown.certificate` proves that a step relation with a strictly
decreasing natural measure produces a result at every fuel above that measure.
Exhaustion is an `Except.error`, distinct from every returned value.
`equals_solution` identifies that result with any independently supplied
defining equation; `value_fixedpoint` connects the ordinary emitted fuel loop
to that equation. These are generic in state, result, environment and measure.

The concrete subject is the actual emitted `FN2-POOL-COMPARE-LOOP` in
`Fn2.Instances.LayerAWorld`. `PoolCompare.certificate` states:

```lean
theorem certificate (a b i n p : Val) :
    ∃ result, (∀ fuel, measure (a,b,i,n,p) < fuel →
      Countdown.run step fuel (a,b,i,n,p) = .ok result) ∧
      result = «FN2-POOL-COMPARE-LOOP» a b i n p
```

The measure is `n.nfix - i.nfix`. All five arguments are arbitrary, including
the pool environment. The generated `step` comes from the canonical admitted
body, with only tail recursion changed to a next-state constructor. The kernel
checks `go_value`, `as_value`, `decreases` and `body_equation`. The independent
canonical term evaluator then proves the loop's body equation with recursive
calls interpreted by its actual emitted function. Its complete body closure is
five functions: the loop, pool data reader, `NATP`, `NFIX`, and `NOT`.

ACL2 checks those five canonical records against the live world and proves both
their body equations and the actual loop's equality to the generated fueled
counterpart:

```lisp
(implies (< (nfix (- (nfix n) (nfix i))) (nfix fuel))
         (equal (fn2-tv-pool-compare-fuel fuel a b i n fn2-pool)
                (fn2-pool-compare-loop a b i n fn2-pool)))
```

Both kernels exercise a nonempty comparison over arbitrary pool data: comparing
one byte with itself needs two units of fuel and returns `(:equal 1)`; one unit
exhausts. Generic controls also exhibit a nondecreasing step that exhausts every
finite budget. This rejects the former possibility of calling stable exhausted
`NIL` an adequate result.

`PrimitiveContracts` proves the integer natives against exact rational
semantics. `floor_faithful` and `ceiling_faithful` cover both signs and zero
divisors. `ash_faithful` proves, for every integer `i` and `c`,
`Native.ash (.int i) (.int c) = .int ⌊(i : ℚ) * (2 : ℚ) ^ c⌋`.
The rational intermediate survives negative shifts; it is never lowered into
integer `Val`. `expt_nonnegative` states the supported direct exponentiation
domain. `rational_intermediate_not_integer_lowering` exhibits the false result
of lowering `2^-1` to the old integer fallback. This is an explicit domain
boundary, not a claim that arbitrary negative `EXPT` is supported by `Val`.

The character contract carries ACL2's byte-character bound; the string
round-trip is universal. Negative ASH with truncation toward zero, signed
division, and CRLF-to-LF normalization controls are checked. The matching ACL2
book proves negative/nonnegative ASH, rational floor/ceiling intervals and both
round trips. Its arithmetic library is local, so its default hints do not leak
into the assembly's different arithmetic library.

The loop's reachable native basis is `CONS`, `INTEGERP`, `<`, `BINARY-+`, `NTH`.
It has no `EXPT`, division, string conversion or rational-producing call site.
The mathematical primitive contracts extend the existing `Faithful` contracts;
the cross-kernel object correspondence remains explicit. This does not certify
every function in the legacy whole-world emission.

Design records are `emit_loop_certificate.py`, `pool_compare.lean.in` and
`print-loop-certificate.lsp`; `emit.sh` invokes them. The proposer uses the
shared canonical transport, syntax-proof generator, ACL2 evaluator generator
and source/dependency/toolchain identity writer. `loop-identity.json` records
the input package and supported closure. The normal `Fn2` root imports the
new modules and the axiom census names their principal statements and controls.

Gates on bb2 (2026-11-08 UTC): primitive REPL 9/9, loop REPL 17/17, no refusals;
`box_certify_bb2.sh bridge-certificate -j 8 books/translation-primitives.lisp
meta/emit/loop-body.lisp` reported **2 built, 0 failed**, taking 0.372 and 16.638
seconds respectively. Countdown, PrimitiveContracts and generated PoolCompare
built; the normal Fn2 import and full census passed with only `propext`,
`Classical.choice`, and `Quot.sound`. The loop book's assembly-loading overhead
still exceeds D26's target; its warm REPL took 1.24 seconds. Evidence is in
`build/bridge-row10-certify.log`, `bridge-loop-load2.log`, and bb2's
`build/bridge-row10-census.log`.
