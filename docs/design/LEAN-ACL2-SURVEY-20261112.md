# Lean ↔ ACL2 & Boyer-Moore/ITP Bridge Survey — Architectural Takeaways for `fn`

**Date:** 2026-11-12  
**Author:** `acl2-lean-scout`  
**Scope:** Complete survey of existing and historical **Lean ↔ ACL2** initiatives (2020–2026) and closely related Boyer-Moore / Lisp ↔ HOL / dependent-type verified stacks, with comparative analysis on (1) untyped `Val`/`SExpr` vs unboxed `BitVec`/stobj array refinement, (2) `:logic` vs `:exec` (`mbe`/`RETURN-LAST`/attachments) soundness, and (3) mechanical proof generation without quadratic kernel blowup, mapped directly to `fn`'s `meta/Fn2/` and `books/translation-validation.lisp`.

---

## 0. Executive Summary

Three direct **ACL2 ↔ Lean 4** systems exist as of November 2026 alongside `fn`'s own two-kernel translation-validation bridge: **`OathTech/ACL2Lean`** (full proof-replay + `SExpr`→Lean type-lifting compiler, presented at ACL2 Workshop 2026), **`Beneficial-AI-Foundation/acl2Ax`** (shallow `Rat`/`CRat` axiom exporter for ACL2 8.7 community books), and AWS Automated Reasoning's ACL2-to-Lean 4 stack (**`leanprover/LNSym`** by ACL2 `x86isa` author Shilpi Goel & Alex Keizer, plus **`leanprover/leansat` / `bv_decide`** porting Centaur GL/Aignet AIG-to-CNF bit-blasting). Across both direct Lean 4 bridges and historical Lisp/ACL2↔HOL stacks (**HOL4-ACL2**, **Milawa/Jitawa**, **Kestrel ATC/ATJ/APT/Aeneas-ACL2**, **Imandra/ImandraX**), every project that scaled past ~50 machine steps converged on the same three architectural laws:

1. **Never expand whole-state tuples or `enc` spines into `cons` lists inside `simp` (`LNSym` `AxEffects` + `ACL2Lean` `SimGen`):** Keep `CoreImage := Fin 57 → Val` (and typed column arrays) symbolic behind an `@[irreducible]` / `simp`-excluded projection barrier; track per-arm mutations in a sparse patch map (`List (Fin 57 × Val)`) so steps touch $O(\text{written children})$ instead of all 57 binders (`c0 .. c56`).
2. **Replace per-arm `simp` tactic scripts with G3-style computational reflection (`ACL2Lean` `DpLift`/`Reflect` + `LNSym` `PruneUpdatesLogic`):** Prove **one** total Lean symbolic stepper (`ArmCert.step` / `WriteBatch.normalize`) sound once in `Fn2.Arms`, and discharge each of `fn`'s 263 arm roots by `rfl` / `decide +kernel` inside an **empty local context** (`Meta.withLCtx {} #[]`, which gave `ACL2Lean` a **13.5×–24.7×** elaboration speedup by hiding outer `World`/child binders from kernel WHNF).
3. **Close `:logic` vs `:exec` (`mbe` / `RETURN-LAST`) in ACL2 world export, never by trusting SBCL (`Kestrel ATC/ATJ` + ACL2 `untranslated-body`):** `fn`'s `Translation.eval_return_last` currently drops the `:exec` branch (`b` in `(RETURN-LAST 'MBE1-RAW exec logic)`). Exporting `symbol-class` (`:common-lisp-compliant` = guard-verified) and `untranslated-body` (or checking guard-verified `mbe` pairs in `books/translation-validation.lisp`) closes the `:logic`/`:exec` seam inside ACL2's kernel without changing `Val` semantics.

### Landscape Matrix

| System / Paper | Years | Authors / Org | Direction & Trust Anchor | Primary URL / Repo |
|---|---|---|---|---|
| **`fn` Bridge** (`Fn2.ACL2`, `Fn2.Arms`, `Fn2.TypedModel`) | 2026 | Ember (`fn`) | Live ACL2 world → canonical S-expr packet → Lean 4 `Translation.evalExport` + `Arms.runCore` equivalence (two-kernel, zero custom axioms) | Local: `docs/design/LEAN-METATHEORY.md`, `BRIDGE-CERTIFICATE.md`, `BRIDGE-GENERATED.md` |
| **`OathTech/ACL2Lean`** (`septract/ACL2Lean`) | 2026 | Mike Dodds, Alok Singh, Claude (Oath Tech; **ACL2 Workshop 2026** tutorial) | Instrumented ACL2 proof log → Lean 4 `evalOpt` proof replay → `derive_exec%` / `derive_sim%` / `mirror_iso%` zero-import pure Lean 4 theorems (checked with `comparator` + `nanoda`) | https://github.com/OathTech/ACL2Lean · https://github.com/septract/ACL2Lean · https://www.cs.utexas.edu/~moore/acl2/workshop-2026/index.html |
| **`acl2Ax`** | 2026 | Christiano Braga (Beneficial AI Foundation / UFF) | ACL2 8.7 `.cert`/books (1,452 catalogued) → shallow Lean 4 `axiom`s over `Rat`/`CRat` + Verso Blueprints | https://github.com/Beneficial-AI-Foundation/acl2Ax |
| **AWS `LNSym`** | 2023–2026 | Shilpi Goel, Alex Keizer, Siddharth Bhat, Henrik Böving, et al. (AWS) | Successor to ACL2 `x86isa`: Armv8 ELF machine code → Lean 4 symbolic simulator (`AxEffects`, `PruneUpdatesLogic`, `bv_decide`) | https://github.com/leanprover/LNSym |
| **Lean 4 `leansat` / `bv_decide`** | 2024–2026 | Henrik Böving (`leanprover`), porting Swords & Davis (ACL2 Centaur GL/Aignet) | AIG bit-blasting + CaDiCaL LRAT certificates reflected in Lean 4 kernel (`BitVec` / `UInt64` automation) | https://github.com/leanprover/leansat · https://arxiv.org/abs/1304.7861 (Swords & Davis) |
| **AWS `Cedar` & `Veil`** | 2024–2025 | Cutler, Hicks, Torlak et al. (`cedar-spec`); Pîrlea, Sergey et al. (`veil`, CAV 2025) | Executable Lean 4 reference semantics + differential random testing (`cedar`) and SMT/Lean state-machine transitions (`veil`) | https://github.com/cedar-policy/cedar-spec · https://github.com/verse-lab/veil |
| **Kestrel `Aeneas → ACL2`** | 2026 | Eric McCarthy (Kestrel Institute; **ACL2 Workshop 2026**) | Charon/LLBC (shared Rust frontend for Lean 4 `SymCrypt` & Aeneas) → ACL2 MIR/functional verification of RustCrypto AES-128 | `acl2/acl2`: `books/workshops/2026/mccarthy-aeneas/`, `books/kestrel/rust/mir/` · Lean counterpart: https://arxiv.org/abs/2609.15648 |
| **Kestrel `ATC` / `ATJ` / `APT` / `Soft`** | 2015–2026 | Alessandro Coglio, Eric Smith, Stephen Westfold, Grant Jurgensen (Kestrel) | Inverse shallow/deep C18 (`ATC`) & Java (`ATJ`) codegen with ACL2 symbolic-execution proofs; isomorphic datatype refinement (`APT` `defiso`) | https://www.kestrel.edu/research/atc/ · https://arxiv.org/abs/2205.11708 · https://arxiv.org/abs/2205.11707 · https://arxiv.org/abs/2009.08565 |
| **`HOL4 ↔ ACL2`** | 2006–2014 | Mike Gordon, Warren Hunt Jr., Matt Kaufmann, James Reynolds (Cambridge / UT Austin) | Deep `sexp` embedding of ACL2 logic in HOL4 + bidirectional `hol2acl2`/`acl22hol` oracle/translation + Reynolds' `encode`/`decode` quotient lifters | https://www.ccs.neu.edu/home/pete/acl206/papers/gordon.pdf · https://www.cl.cam.ac.uk/archive/mjcg/acl214slides.pdf |
| **`Milawa → Jitawa → HOL4`** | 2009–2016 | Jared Davis & Magnus O. Myreen (UT Austin / Centaur / Cambridge) | Self-verifying 11-layer reflective ACL2-like prover (`Milawa`) proved sound on verified x86-64 Lisp runtime (`Jitawa`) in HOL4 | https://www.cl.cam.ac.uk/~mom22/jitawa/ · https://doi.org/10.1007/s10817-015-9324-6 |
| **Imandra / ImandraX + ACL2 Real SOS Bridge** | 2020–2026 | Grant Passmore, Matt Kaufmann, et al. (Imandra / UT Austin) | Typed OCaml computational HOL with Boyer-Moore waterfall (`ImandraX`); verified Positivstellensatz nonlinear certificate bridge into ACL2 (ACL2-2023) | https://arxiv.org/abs/2004.10263 · https://arxiv.org/abs/2311.08861 · https://imandrax.dev/docs/ |
| **Isabelle/Coq/Why → ACL2 (`XLL`) & `Dracula`** | 2008–2014 | J. Heras, J. Aransay, V. Pascual (`XLL`); C. Eastlund & M. Felleisen (`Dracula`) | First-order Coq/Isabelle specs → XML (`XLL`) → ACL2; ML-style modular interfaces (`refined-acl2`) compiled to ACL2 `encapsulate` | https://arxiv.org/abs/1303.1420 · https://doi.org/10.1007/978-3-540-92995-6_4 |

---

## 1. Direct Lean ↔ ACL2 Initiatives (2024–2026)

### 1.1 `OathTech/ACL2Lean` — Full Proof-Replay & Type-Lifting Compiler (Dodds, Singh, Claude, 2026)
**Claim & scope:** `OathTech/ACL2Lean` (~70 KLOC Lean 4.33 + instrumented ACL2 fork, `https://github.com/OathTech/ACL2Lean`, presented by Mike Dodds at ACL2 Workshop 2026) is the only end-to-end **proof-replaying** ACL2-to-Lean 4 pipeline, replaying **116/116** corpus theorems unconditionally and lifting **21** theorem products (including all 15 theorems of J Moore's sorting corpus: `isort`, `msort`, `qsort`, `bsort`) to zero-import pure Lean 4 checked by `leanprover/comparator` and the Rust kernel `nanoda`.

- **Architecture (9 stages across 3 tiers):**
  1. **ACL2 trace extraction:** An instrumented ACL2 fork (`fork/` submodule, 228 `TRACE-LOG[...]` tags across 12 source files) emits S-expression proof logs parsed into JSON (`tools/extract_trace.py`).
  2. **Deep evaluator (`ACL2Lean/Base/Eval.lean`, `World.lean`):** Models `SExpr` (`atom (a : Atom)` | `cons (car cdr : SExpr)`), `World` (`DefMap := List (SExpr × DefEntry)`), and fuel-bounded `evalOpt : Nat → World → Env → SExpr → Option SExpr`. Crucially, `evalOpt` returns `Option SExpr` rather than `Except String SExpr` because `none = none` holds definitionally before fuel convergence, enabling fuel-monotonicity and fuel-equality lemmas without error-string divergence (`Fn2.ACL2.Translation.evalExport` uses `Except String Val`, which forces explicit `.ok` hypotheses before comparing fuels).
  3. **Replayed statement (`ACL2Lean/Proofs/`):** Proves `EvTrue w env (disjoinTerm cl)` (`∃ fuel v, evalOpt fuel w env t = some v ∧ v ≠ nil`) by replaying waterfall clause steps (`simplify`, `destruct`, `fertilize`, `clausify`, `induction`, `linear`, `type-set`, `executable-counterpart`).
  4. **Waypoint (`ACL2Lean/Imported/`, `ExecGen.lean`, `SimGen.lean`):** `derive_exec%` synthesizes structural/well-founded Lean functions `f : SExpr → SExpr`; `derive_sim%` proves `∃ fuel, evalOpt fuel w env (.call f args) = some (f_lean ...)`.
  5. **Zero-import Mirror (`ACL2Lean/Mirrors/`, `IsoGen.lean`, `TransportGen.lean`):** `mirror_iso%` proves `f_lean (Rep.enc x) = Rep.enc (f_mirror x)` over native Lean types (`List Int`, `Nat`, `Option Int`); `mirror_transport%` strips all `SExpr`/`ACL2Lean` imports, leaving pure `Std`-only Lean 4 theorems.
- **Assurance bugs caught during `ACL2Lean` development (directly relevant to `fn`):**
  - **BUG-012 (`SExpr` non-canonical rationals):** If `Number.rational num den` lacks a baked-in reducedness proof (`den > 0 ∧ Nat.Coprime num.natAbs den`), Lean's structural `BEq`/`DecidableEq` distinguishes unreduced fractions that ACL2's `EQUAL` identifies, falsifying reflexivity/equality transfer. (`fn`'s `Fn2.ACL2.Val.rat` should keep reduced invariants explicit whenever rationals enter primitive equality.)
  - **BUG-019 ("Failed GREEN" via `encapsulate` witness leakage):** Exporting ACL2's internal world naively exported local `encapsulate` witnesses (`(lambda (x) '0)`), so Lean proved theorems about constant zero instead of universally quantified constrained functions! `fn` avoids this cleanly via `books/translation-validation.lisp:223-228` (`fn2-tv-refused-functions` checking `(not (getpropc fn 'unnormalized-body nil world))` and `(not (fn2-tv-attachment fn world))`), which is an architectural strength `fn` already possesses over early `ACL2Lean`.

### 1.2 `Beneficial-AI-Foundation/acl2Ax` — Shallow `Rat`/`CRat` Axiom Exporter (Braga, 2026)
**Claim & scope:** `acl2Ax` (`https://github.com/Beneficial-AI-Foundation/acl2Ax`, Lean v4.34.0, Nov 2026) translates 5 ACL2 8.7 community book suites (`arithmetic`, `arithmetic-2`, `arithmetic-3`, `std`, `kestrel/utilities`, out of 1,452 catalogued books) into shallow Lean 4 `axiom` declarations paired with Verso Blueprints embedding `.cert` hex dumps.

- **Mechanism & cautionary lesson (`EMBEDDING_DECISIONS.md` & `Lean/ACL2/Base.lean`):** `acl2Ax` maps ACL2 numbers to `Rat` (and complex rationals `CRat`), lists to `List Rat`, and `realrationalp x := True`. Because ACL2 variables range over the **entire untyped universe** (where `(ACL2-NUMBERP 'FOO) = NIL` and `(+ 'FOO 1) = 1` via `fix`), narrowing unconstrained variables to `Rat` silently drops non-numeric counterexamples, while conversely mapping `integerp : Rat → Prop` requires explicit subtype hypotheses. `acl2Ax`'s 2026-11-10 commit history had to retrofit `CRat` after `acl2-numberp` vs `rationalp` conflation broke complex-rational theorems. This validates `fn`'s D-metatheory choice (`LEAN-METATHEORY.md` §3): **never axiomatize shallowly translated ACL2 theorems in Lean; refine from the deep `Val` semantics via proved simulation (`Fn2.TypedModel`).**

### 1.3 AWS Automated Reasoning: `LNSym`, `leansat` (`bv_decide`), `Cedar`, and `Veil`
**Claim & scope:** AWS's hardware/cryptography verification group migrated its symbolic-simulation methodology from ACL2's `x86isa` and Centaur `GL` into Lean 4 via **`leanprover/LNSym`** and **`leanprover/leansat`**, developing state-update reflection tactics that directly solve `fn`'s 57-child / 67-column `simp` bottleneck.

- **`leanprover/LNSym` (`https://github.com/leanprover/LNSym`):** Led by **Shilpi Goel** (co-author of ACL2's stobj-based `x86isa` at UT Austin/Centaur) with **Alex Keizer**, **Siddharth Bhat**, and **Henrik Böving**, `LNSym` verifies Armv8 production crypto (`AWS-LC` AES-GCM, SHA-512) directly in Lean 4 without ACL2's untyped Lisp reader or trust tags. Two files in `LNSym` are blueprints for `@bridge-gen`:
  1. `Arm/Insts/Common/AxEffects.lean` (*Axiomatic Effects*, Alex Keizer): Tracks symbolic state updates in a meta-level `Std.HashMap StateField FieldEffect` storing `(valExpr, effectProof : r fld curState = val)` per touched field plus a single `nonEffectProof : ∀ f ∉ touched, r f curState = r f origState`. Untouched registers/fields are **never** unfolded or rewritten at intermediate instructions.
  2. `Tactics/PruneUpdates.lean` & `Tactics/PruneUpdatesLogic.lean` (Shilpi Goel): Reflects chains of state writes `w f₁ v₁ (w f₂ v₂ ... s)` into a syntax list `ArmConstr.Updates` indexed by `Nat` context IDs, runs a verified canonicalizer/deduplicator (`eraseReps`) in the kernel via `decide`/`rfl`, and eliminates shadowed/reordered writes in one step instead of $O(k^2)$ `simp` commutation rules.
- **`leanprover/leansat` / `bv_decide` (`https://github.com/leanprover/leansat`):** Explicitly implements **Sol Swords & Jared Davis's ACL2 Centaur GL / Aignet AIG-to-CNF algorithm** (*"Verified AIG Algorithms in ACL2"*, ACL2-2013, `arXiv:1304.7861`) inside Lean 4's standard library, checking CaDiCaL LRAT unsat certificates in the Lean kernel. For `fn`'s `Fn2.TypedModel` (`BitVec 8`, `BitVec 60`, `BitVec 64` wire/ticket arithmetic), `bv_decide` gives Centaur-GL-grade bit-blasting natively in Lean 4 with zero external axioms.
- **`cedar-spec` & `veil` (`https://github.com/cedar-policy/cedar-spec`, `https://github.com/verse-lab/veil`):** Pair idiomatic executable Lean 4 models with millones-of-runs differential testing against production Rust (`cedar`) and small-model SMT/Lean invariant synthesis (`veil`), mirroring `fn`'s `fn2-measure` differential discipline (`LEAN-METATHEORY.md` §10).

### 1.4 Kestrel Institute & ACL2 Workshop 2026 (`Aeneas → ACL2`, `ATC`, `ATJ`, `APT`)
**Claim & scope:** Kestrel Institute has no standalone ACL2→Lean translator, but at **ACL2 Workshop 2026** (Nov 16–18, 2026) Eric McCarthy connected the **Charon/Aeneas** Rust verification pipeline (used in Lean 4 for Microsoft's `SymCrypt`, `arXiv:2609.15648`) directly to ACL2, while Alessandro Coglio's `ATC`/`ATJ`/`APT` suite established the canonical ACL2 patterns for isomorphic type refinement and `:exec` verification.

- **McCarthy, *"Verifying RustCrypto's Fixsliced AES-128 in ACL2: An Aeneas Backend and an Executable MIR Semantics"* (ACL2-2026, `books/workshops/2026/mccarthy-aeneas/`, `books/kestrel/rust/mir/`):** Adds an ACL2 backend to Inria/Microsoft's Aeneas (which already targets **Lean 4**, HOL4, Coq, F*), enabling shared LLBC intermediate representations across Lean 4 and ACL2.
- **Coglio, `ATC` (`arXiv:2205.11708`), `ATJ` (`arXiv:2205.11707`), and Coglio & Westfold `APT` (`defiso`, `arXiv:2009.08565`):** Generates modular per-function symbolic-execution theorems in ACL2 relating shallowly typed ACL2 representations (`sint`, `uint`, heap-array stobjs) to a deep C18 operational semantics (`exec-fun`, `exec-stmt`), using `:expand :lambdas` and exact rule-set theories so generated proofs scale linearly in AST size.

---

## 2. Closely Related Lisp / Boyer-Moore ↔ HOL / ITP Stacks

1. **`HOL4 ↔ ACL2` (Gordon, Hunt, Kaufmann, Reynolds, 2006–2014):** Deeply embedded ACL2's `sexp` universe (`sym`, `str`, `chr`, `num (com (rat ...))`, `cons`) and axioms in HOL4 (`examples/acl2/` in HOL4 repo; FMCAD 2006, ACL2-2006, J. Symbolic Computation). Proving ACL2's axioms in HOL4 famously exposed subtle bugs in ACL2's early axiom packaging. **James Reynolds' PhD thesis (*"Automatic Translation of HOL Functions into ACL2"*, Cambridge, 2010)** solved the `sexp` ↔ HOL type gap via composable **`encode`/`decode` partial-bijection lifters** (`detype` theorems): every HOL type `α` carries `encode : α → sexp`, `decode : sexp → α`, and `detect : sexp → bool` (`∀ x, detect (encode x) ∧ decode (encode x) = x`), automatically rewriting untyped `|= acl2_thm` theorems into typed HOL theorems without exposing `sexp` constructors to the user.
2. **`Milawa → Jitawa → HOL4` (Davis & Myreen, ITP 2011, JAR 2015 `10.1007/s10817-015-9324-6`):** Verified an ACL2-style theorem prover down to x86-64 machine code in HOL4. Two architectural pillars directly inform `fn`:
   - **Reflective tower (`level 2 .. level 11`):** Instead of emitting giant kernel proof scripts per theorem, Milawa verifies increasingly rich *proof builders* (clause simplifiers, rewriters, Boyer-Moore waterfall) as ordinary terminating Lisp functions and switches to them via a single reflection principle, shrinking proof certificates by orders of magnitude.
   - **Two-stage `Sexp` → flat-array memory refinement (`Jitawa`):** Refines pure Lisp `Sexp` values first to an abstract heap graph with explicit garbage-collection/bounds invariants, and second to unboxed 64-bit tagged words in a flat byte/word array—never reasoning about byte layout and Lisp evaluation rules in the same proof step.
3. **Imandra / ImandraX & the Imandra↔ACL2 Bridge (Passmore, Kaufmann, et al., `arXiv:2004.10263`, `arXiv:2311.08861`):** `ImandraX` implements the Boyer-Moore waterfall directly over a **statically typed, higher-order pure subset of OCaml (`IML`)**, eliminating `mbe` type-coercion boilerplate (`nfix`, `ifix`) at the root because functions carry native algebraic/numeric types and execute unboxed in OCaml. In **ACL2-2023 (`arXiv:2311.08861`, *"ACL2 Proofs of Nonlinear Inequalities with Imandra"*)**, Passmore & Kaufmann bridged Imandra to ACL2 via **untrusted certificate search + verified ACL2 rational Positivstellensatz checker**—the exact certificate-checker pattern `fn` uses in reverse.
4. **Coq/Isabelle → ACL2 (`XLL`, Heras, Aransay, Pascual, `arXiv:1303.1420`) & `Dracula` (`refined-acl2`, Eastlund & Felleisen, PADL 2009):** `XLL` translates first-order Coq/Isabelle specs into ACL2 to harvest Boyer-Moore induction hints, while `Dracula` compiles ML-style modular signatures into ACL2 `encapsulate` + `defattach`-style obligations.

---

## 3. Comparative Analysis on the Three Core Problems (Mapped to `fn`)

### 3.1 Untyped Lisp `Val` vs Typed / Unboxed `BitVec` / Stobj Array Refinement

| Design Axis | `fn` Today (`Fn2.TypedModel` & `Arms`) | `ACL2Lean` (`Lifting.lean` / `SimGen.lean`) | `HOL4-ACL2` (Reynolds) & `Jitawa` | **Concrete Upgrade for `fn` (`Fn2.TypedModel` PW4 & `Fn2.Arms`)** |
|---|---|---|---|---|
| **Type relation** | `TypedCol.α : TypedCol c → Val` (`Val.ofList (xs.map encodeCell)`), one-way abstraction + `TableWfp` | `Rep α` (`enc`, `inj`, `recog : SExpr → Prop`, `mem`), full subtype bijection `α ≃ {s // recog s = t}` | `(encode, decode, detect)` Galois retraction (`decode (encode x) = x`) | Add `decodeCell` + retraction `decodeCell (encodeCell x) = x` to `ColSpec` (`TypedModel.lean:36-78`). Retraction makes simulation compose forward *and* backward without existential witnesses! |
| **Runtime backing store** | `List (BitVec c.width)` (functional singly-linked cons list; $O(n)$ `List.set`/`getD`) | `List α` / `Int` for sorting corpus (`Std` mirrors) | `Jitawa` & `ATC`: flat fixed-capacity word/byte `Array` (`UInt8`/`UInt64`) | Replace `List (BitVec c.width)` in `TypedCol` with **`Array (BitVec c.width)`** (and `ByteArray` for octet buffers/arena slices). Lean 4's runtime mutates `Array`/`ByteArray` **in-place** when reference count = 1 (matching ACL2 stobj single-threadedness!) while keeping pure `Array.toList` logic lemmas. |
| **`simp` firewall** | `image kids` and `TypedCol.α` unfold to `Val.ofList (List.ofFn ...)` (`57` `Val.cons` nodes!) | `SimGen` marks `-Logic.car, -Logic.cdr, -Logic.cons` and keeps all terms in **`Rep.enc xs` normal form** | Reynolds' rewrite tactics never unfold `encode` | Mark `CoreImage.toVal` (`image`) and `TypedCol.α` `@[irreducible]` (or `simp`-opacified) with indexed read/write bridge lemmas (`nth_image`, `updateNth_image`) so `Val.cons` spines **never** materialize in proof goals. |
| **PW4 Direction A vs B** (`LEAN-METATHEORY.md` §7.2) | Open question: `defop` dual emission (A) vs `LayerAWorld` refinement (B) | `derive_exec%` → `derive_sim%` → `mirror_iso%` (2-hop **Direction B** via `fun_induction`) | `APT` `defiso` + `ATC` (stepwise **Direction B**) | **Choose Direction B via a Typed Table Spec layer (`derive_sim`-style):** Do NOT trust a second `defop` generator path (Direction A creates a new unverified emission surface). Instead, lift ACL2's generated table accessors (`FN2-<KIND>-<COL>`, `FN2-<KIND>-SET-<COL>`) *once per table* against `LayerAWorld` (`TypedCol.α`), then lift `runArm` against `TypedCore` compositionally. |

### 3.2 `:logic` vs `:exec` (`mbe` / `RETURN-LAST` / `defattach`) Soundness

**The exact seam in `fn` today:**
- In `meta/Fn2/ACL2/Translation.lean:87` & `153-155`, `RETURN-LAST` evaluates **only** its final (`:logic`) argument:
  ```lean
  | "RETURN-LAST", [_, _, x] => evalExport fuel x fns env
  ```
- Why ACL2 puts `RETURN-LAST` there: When ACL2 admits `(mbe :logic L :exec E)` (or `prog2$`, `time$`, stobj `let` bindings), ACL2's macroexpander translates `(mbe :logic L :exec E)` into `(RETURN-LAST 'MBE1-RAW E L)` inside `unnormalized-body` (`books/translation-validation.lisp:45`).
- In ACL2's own kernel, SBCL only runs `E` instead of `L` **if and only if** the function is **guard-verified** (`(eq (getpropc fn 'symbol-class nil world) :common-lisp-compliant)`), which requires ACL2 to have proved `(implies guard (equal L E))` and verified guards of all callees, and no `defattach` overrides `fn` (already checked by `fn2-tv-attachment` in `books/translation-validation.lisp:33-40` and `Translation.Manifest.accepts`!).
- **What happens if `fn` ever runs Lean as a compiled binary or claims `:exec` fidelity:** Evaluating `unnormalized-body` via `eval_return_last` executes `L` (e.g., slow list/integer spec), whereas SBCL executes `E` (fast fixnum/ash/stobj path)—and if a function in the served closure were *not* `:common-lisp-compliant`, `L` and `E` would not even have an ACL2 guard-equivalence proof!

**How other systems handle `:logic` vs `:exec` and what `fn` should do:**
1. **`Kestrel ATJ` (`arXiv:2205.11707`) & `ATC` (`arXiv:2205.11708`):** Refuse to extract executable target code from `unnormalized-body` alone when `:exec` matters; they inspect ACL2's **`untranslated-body`** (or require `guard-verified-p` = `t`) and generate equivalence obligations on `(mbe :logic L :exec E)` so the generated code runs `E` while inheriting theorems proved on `L`.
2. **`ACL2Lean` (`gen-world`):** Fail-closed rejects `mbe`/unverified `:exec` constructs until guard preconditions are carried in the replay obligation.
3. **Concrete 10-line hardening for `fn` (`books/translation-validation.lisp`):**
   - Add `:symbol-class (fn2-tv-object (fn2-tv-property fn 'symbol-class world))` to `fn2-tv-function` (`books/translation-validation.lisp:41-50`)—or assert in `fn2-tv-served-closure-p` that every served root (`fn2-turn`, `fn2-host-*`, arm roots) has `(eq (getpropc fn 'symbol-class nil world) :common-lisp-compliant)`. That mechanically binds ACL2's kernel guard-verification proof (including `(implies guard (equal exec logic))` for every `mbe` in the call DAG!) directly into the checked export certificate!
   - If `fn` later compiles Lean `Fn2` to native code (`LEAN-METATHEORY.md` §11 Path 3), emit a parallel `evalExec` interpreter (or `:exec` lowering) that takes `b` in `(RETURN-LAST 'MBE1-RAW b c)` when the exported guard holds, justified by the exported `:symbol-class :common-lisp-compliant` certificate.

---

### 3.3 Scaling Mechanical Per-Arm Certificates from `26/263` to `263/263` Without Quadratic Kernel Blowup

**Diagnosis of `fn`'s current certificate bottlenecks (`Validation.lean`, `CoreValidation.lean`, `core_draining.lean.in`, `emit_served_certificate.py`):**
1. **`57`-binder spine explosion (`c0 .. c56`):** `idle_validation.lean.in` and `CoreValidation.lean` generate theorems quantifying 57 explicit variables `(c0 : Val) ... (c56 : Val)`, pass `Val.ofList [c0, ..., c56]` into `simp`, unfold `List.ofFn_succ` 57 times in `echo_free_whole_core`, and emit up to **67 per-column `.core_call` helper theorems** per machine kind (`CoreValidation.lean:353-588`). Across 263 roots, that is ~15,000 outer binders and thousands of helper declarations.
2. **$O(k^2)$ `fieldWrite_order` sorting in `simp` (`core_draining.lean.in:62-65`):** Flushing $k$ column updates (`:set` / `:next`) commutes writes into table column order using manual pairwise `fieldWrite_order i j` lemmas inside `simp (disch := decide) only [...]` (15 pairwise lemmas for 12 columns in `CNS :DRAINING`; for a 30-column flush, $\binom{30}{2} = 435$ rewrite pairs!).
3. **Ambient-context `simp` / `decide` tax (`ACL2Lean` Perf Profile Finding P6):** Running `simp` and `decide +kernel` inside goals whose local context `LCtx` holds 60+ `Val` hypotheses and unfolded `Val.ofList` terms causes Lean 4's congruence/WHNF engine to scan the local context repeatedly (`13.5×` slowdown measured in `ACL2Lean`).

#### Five Concrete Mechanisms for `@bridge-gen` (`sprint-bridge-gen`)

##### Mechanism 1: Sparse `CoreImage` Frame (`LNSym` `AxEffects` pattern) — Kill `(c0 : Val) .. (c56 : Val)`
Keep `kids : Fin N → Val` (`N = 57` for `:core` arms, `N = tuple.length` for `:children` subarms) **universally quantified as a single function variable `kids`** throughout every lemma—never instantiate `c0 .. c56`!
- Define in `meta/Fn2/Arms/` (shared across all 263 roots):
  ```lean
  def stobjsOfTuple (tuple : List String) (kids : Fin tuple.length → Val) : Env :=
    List.ofFn (fun i : Fin tuple.length => (tuple[i], kids i))

  def CorePatch (n : Nat) := List (Fin n × Val)
  def applyPatch {n} (kids : Fin n → Val) (p : CorePatch n) : Fin n → Val := ...
  ```
- Prove **once** in `Fn2.Arms`:
  - `lookup_stobjsOfTuple (i : Fin tuple.length) (hnd : tuple.Nodup) : lookup (stobjsOfTuple tuple kids) tuple[i] = some (kids i)`
  - `putStobj_stobjsOfTuple` updating `kids` via `Function.update kids idx newVal` (discharged by `decide +kernel` on `idx : Fin 57`!).
  - `rowReads_of_tableSpec` parameterized by a compact `KindTableSpec` data record (one per *machine kind* = **14 specs total**, NOT once per arm = 263 times!). That immediately eliminates duplicating `cns_row_reads` / `echo_row_reads` across all 263 `Root<N>Proof.lean` files!

##### Mechanism 2: Reflective Write-Batch Canonicalizer (`LNSym` `PruneUpdatesLogic` pattern) — Kill $O(k^2)$ `fieldWrite_order`
For `pending-write/phase-update certificate` (`:set` / `:next` + `flush`), every machine table row is updated by nested `UPDATE-NTH colIdx val row` (`fieldWrite`).
- Instead of commuting `fieldWrite` calls with $O(k^2)$ `simp` rules (`core_draining.lean.in:65`), define a tiny reflected write-batch normalizer in `meta/Fn2/Arms/`:
  ```lean
  abbrev ColUpdates := List (Nat × Val)
  def applyColUpdates (row : Val) : ColUpdates → Val
    | [] => row
    | (c, v) :: rest => applyColUpdates (Native.updateNth (.int c) v row) rest

  /-- Canonical insertion/merge sort by column index, keeping the LAST write to each column. -/
  def canonColUpdates (u : ColUpdates) : ColUpdates := ...

  theorem applyColUpdates_canon (row : Val) (u : ColUpdates) :
      applyColUpdates row u = applyColUpdates row (canonColUpdates u)
  ```
- Prove `applyColUpdates_canon` **once** (using `updateNth` commute for `i ≠ j` and shadow for `i = j`). Then for *any* arm flushing $k$ columns in arbitrary DSL order vs ACL2's emitted order, equating the two write chains reduces to `canonColUpdates u_interp = canonColUpdates u_emitted`—a single $O(k \log k)$ **`rfl`** check when values match syntactically (or a linear `congrArg` list match when values contain symbolic expressions)!

##### Mechanism 3: Compositional Statement-Combinator Hoare/CPS Lemmas (`ACL2Lean` G3 + `ATC` modular rules)
Instead of monolithic per-arm `simp` transcripts, match `BRIDGE-GENERATED-COVERAGE.txt`'s 4 missing obligation classes with **4 compositional CPS/stepping lemmas** in `meta/Fn2/Arms/` over `run w f fuel st (stmt :: rest)`:
1. **`run_set` / `run_next` + `flush_eq_canon`:** Pushes `(col, val)` onto `st.pending` without touching `st.stobjs`, then discharges `flush` via `applyColUpdates_canon` + a single `KindFitSpec` check (`unsigned_fits` / `signed_fits` proved once per column width `.uw w` / `.sw w`).
2. **`run_do` / `run_issue` (`operation-result and child-writeback certificate`):** Parameterize by a 1-per-operation `OpCallSpec` (**~60 operations total** in `:OPERATIONS`, shared across all 263 arms!) stating `callFn world opName args = .ok (opFn args)` and splitting `:case` / `:ok` / `:refused` outcomes while updating only the operation's `:returns` indices in `kids : Fin N → Val`.
3. **`run_if` / `run_cond` / `run_case` (`branch-join certificate`):** A single syntax-directed lemma `run_if_split` that splits `if (evalExpr ...).truthy` on the interpreter side in lockstep with `Val.truthy_ite` on the emitted ACL2 function side, so `emit_served_certificate.py` emits recursive tree-structured proofs mirroring the arm's AST (`statement_words` walker in `emit_served_certificate.py:305-333` already parses every branch!).
4. **`run_stop` / `run_halt` & `run_goto` (`stop/reclamation` & `subarm-composition`):**
   - For `:goto subarmTag`: **Prove `:SUBARMS` roots first in topological order!** Because every subarm already has a `Root<M>.contract` (`emit_served_certificate.py:240-255`), a parent arm's `:goto` step simply **rewrites by `Root<M>Proof.validated`** (with fuel `fuel_parent = 1 + fuel_steps + fuel_subarm`) instead of re-proving the subarm inline! That turns deep `FN2-CURSOR-*`, `FN2-CNS-*`, and `FN2-AUTH-*` subarm DAGs from exponential path blowup into **$O(1)$ lemma application per `:goto` edge**!

##### Mechanism 4: Empty-Context Subproofs & Narrowed World Imports (`ACL2Lean` Perf Arc P6 & D7)
- **Kind-shared modules (`ServedKind<K>Common.lean`):** Put `snapshot_bounds`, `rowReads`, column `.core_call` dispatch lemmas, and `KindTableSpec` **once** per machine kind (`14` files) rather than repeating them in each of the `263` `Root<N>Proof.lean` files (`idle_validation.lean.in` currently re-proves `rowReads` in every single root!).
- **Narrowed `import all` slices (`emit_embed.py`):** Import only the `LayerAWorld` shard files containing functions in that root's shallow 1-step call set (already implemented for `CoreValidation.lean:13-52` via `emit_embed.py` scan—reuse that exact scanner for generated `Root<N>Proof.lean` files!).
- **Closed helper lemmas (`LCtx` hygiene):** Emit ground side-condition checks (`nativeCall_none`, index lookups, signature equality) as top-level `private theorem ... := by decide +kernel` or `by rfl` **outside** the `kids` / `id` / `budget` binders, or prove them with `rfl` where possible (`rfl` avoids elaborating `Decidable` instances entirely). Also note `ACL2Lean`'s Lean 4 discovery: inside custom `MetaM` tactics, `withOptions (maxHeartbeats := ...)` is a **no-op**; heartbeat caps live on `Core.Context.maxHeartbeats`.

##### Mechanism 5: Eliminating the 103s ACL2 `served-export.lisp` D26 Bottleneck (Future / Gate Speedup)
`BRIDGE-GENERATED.md:97` notes `served-export.lisp` takes ~103–105s (mostly loading `books/reference` + checking 12,039 packed records). Two ways to cut this:
1. Pre-certify a thin `books/served-export-base.lisp` that includes `books/reference` + `books/translation-validation` once (so `served-export.lisp` loads one warm `.cert`/sysfile closure in ~5–8s), and
2. In `fn2-tv-matches-packed-functions` (`books/translation-validation.lisp:180`), compile `fn2-tv-unpack` and `fn2-tv-codes` with `:guard t` (`verify-guards t`) instead of `:verify-guards nil` (`books/translation-validation.lisp:161`): in ACL2, `:verify-guards nil` forces `make-event` evaluation through ACL2's **interpreted logic evaluator** rather than compiled raw Common Lisp, costing a 5×–20× slowdown over 12,039 function ASTs!

---

## 4. Primary References & Exact Citations

1. **Dodds, M., Singh, A., & Claude (2026).** *ACL2Lean: Mechanically Lifting ACL2 Proofs and Functions to Pure Lean 4.* Oath Technologies. Repository: https://github.com/OathTech/ACL2Lean (mirror: https://github.com/septract/ACL2Lean). Tutorial at *19th International Workshop on the ACL2 Theorem Prover and Its Applications (ACL2 2026)*, Nov 16–18, 2026, SRI International: https://www.cs.utexas.edu/~moore/acl2/workshop-2026/index.html.
   - Key source files inspected: `ACL2Lean/Base/Reflect.lean` (positional congruence walker + `proveByDecide` `Expr` cache), `ACL2Lean/Base/Lifting.lean` (`Rep α`, `Implements`), `ACL2Lean/Tactics/SimGen.lean` (`enc`-normal-form `simp` firewall), `ACL2Lean/Tactics/IsoGen.lean` (`mirror_iso%` via `fun_induction`), `docs/dev/2026-06-11_perf-profile.md` (Finding P6: `Meta.withLCtx {} #[]` 13.5×–24.7× speedup), `docs/dev/2026-08-17_perf-arc-charter.md` (`evalOpt_world_mono`).
2. **Braga, C. (2026).** *acl2Ax: Exporting ACL2 8.7 Community Books to Lean 4.* Beneficial AI Foundation / Universidade Federal Fluminense. Repository: https://github.com/Beneficial-AI-Foundation/acl2Ax (`EMBEDDING_DECISIONS.md`, `Lean/ACL2/Base.lean`).
3. **Goel, S., Keizer, A., Bhat, S., Böving, H., et al. (2023–2026).** *LNSym: Armv8 Symbolic Simulator and Cryptographic Verification in Lean 4.* AWS Automated Reasoning / `leanprover`. Repository: https://github.com/leanprover/LNSym (`Arm/Insts/Common/AxEffects.lean`, `Tactics/PruneUpdates.lean`, `Tactics/PruneUpdatesLogic.lean`).
4. **Böving, H. (2024–2026) & Swords, S., Davis, J. (2013).** *leansat / `bv_decide`* (https://github.com/leanprover/leansat), implementing verified AIG-to-CNF bit-blasting from Swords & Davis, *"Verified AIG Algorithms in ACL2"*, ACL2 Workshop 2013, EPTCS 114, pp. 95–108, https://arxiv.org/abs/1304.7861.
5. **McCarthy, E. (2026).** *"Verifying RustCrypto's Fixsliced AES-128 in ACL2: An Aeneas Backend and an Executable MIR Semantics."* ACL2 Workshop 2026 (`acl2/acl2`: `books/workshops/2026/mccarthy-aeneas/`, `books/kestrel/rust/mir/`). Lean 4 Aeneas counterpart: Fromherz & Protzenko, *"Verifying Symmetric Cryptography in Lean 4 with SymCrypt"*, 2026, https://arxiv.org/abs/2609.15648.
6. **Coglio, A. (2022).** *"A Proof-Generating C Code Generator for ACL2 Based on a Shallow Embedding of C in ACL2 (ATC)."* ACL2 Workshop 2022, EPTCS 359, pp. 119–136, https://arxiv.org/abs/2205.11708 · *"A Complex Java Code Generator for ACL2 (ATJ)"*, https://arxiv.org/abs/2205.11707 · Coglio, A. & Westfold, S. (2020), *"Isomorphic Data Type Transformations (APT `defiso`)"*, ACL2 Workshop 2020, EPTCS 327, https://arxiv.org/abs/2009.08565.
7. **Gordon, M., Hunt, W. A., Kaufmann, M., & Reynolds, J. (2006–2010).** *"An Embedding of the ACL2 Logic in HOL"* (ACL2-2006, https://www.ccs.neu.edu/home/pete/acl206/papers/gordon.pdf); *"An Integration of HOL and ACL2"* (FMCAD 2006); Reynolds, J. (2010), *"Automatic Translation of HOL Functions into ACL2"*, Technical Report UCAM-CL-TR-784, University of Cambridge.
8. **Davis, J., & Myreen, M. O. (2011, 2015).** *"A Verified Runtime for a Verified Theorem Prover (Jitawa)"*, ITP 2011 (https://www.cl.cam.ac.uk/~mom22/jitawa/itp2011-draft.pdf); *"The Reflective Milawa Theorem Prover is Sound (Down to the Machine Code that Runs it)"*, Journal of Automated Reasoning 55(2), 2015, https://doi.org/10.1007/s10817-015-9324-6.
9. **Passmore, G., Cruanes, S., Ignatovich, D., et al. (2020); Passmore, G., Kaufmann, M., et al. (2023).** *"The Imandra Automated Reasoning System"*, IJCAR 2020, https://arxiv.org/abs/2004.10263; *"ACL2 Proofs of Nonlinear Inequalities with Imandra"*, ACL2 Workshop 2023, EPTCS 393, https://arxiv.org/abs/2311.08861.
10. **Cutler, J., Hicks, M., Torlak, E., et al. (2024).** *Cedar Specification & Differential Verification in Lean 4*, https://github.com/cedar-policy/cedar-spec · **Pîrlea, G., Sergey, I., et al. (2025).** *Veil: Automated Protocol Verification in Lean 4*, CAV 2025, https://github.com/verse-lab/veil.
11. **Heras, J., Pascual, V., Rubio, J., et al. (2013); Aransay, J., et al. (2014).** *"Verifying a Platform for Digital Imaging: A Multi-Tool Strategy (Coq/Isabelle → XLL → ACL2)"*, https://arxiv.org/abs/1303.1420 · **Eastlund, C., & Felleisen, M. (2009).** *"Toward a Practical Module System for ACL2 (`Dracula`)"*, PADL 2009, https://doi.org/10.1007/978-3-540-92995-6_4.
