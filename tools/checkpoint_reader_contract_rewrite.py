#!/usr/bin/env python3
"""Partition the actual descriptor-reader carrier metadata; no formula copies.

The captured before fixture is the original sixteen-facet invocation. The
transformation preserves its arguments, carrier options and hints verbatim.
"""
from pathlib import Path
import sys
import lisp_rewrite as lr
import reader_foundation_batch as rw

ROOT = Path(__file__).resolve().parents[1]
PATTERN = '(fn2-checkpoints-preserves fn2-checkpoint-check-step ?*body)'

HELPER = '''; Six original unrestricted facets have concrete logical counterexamples.
; Generate their exact old formulas from the same metadata as the ten retained
; facets. No guarded replacement is a proof of an unrestricted original.
(local (defun fn2-checkpoint-reader-partition-contracts (args specs facts)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (let* ((fact (car facts)) (position (caddar specs))
         (negative (cdr (assoc-equal position
                       '((4 . fn2-checkpoint-reader-checker-domain-removal-check)
                         (5 . fn2-checkpoint-reader-hasher-domain-removal-check)
                         (8 . fn2-checkpoint-reader-digests-domain-removal-check))))))
   (cons (if negative
          `(defthm-owed ,(cadr fact) ,args ,(caddr fact)
            :teeth (fn2-checkpoint-reader-guard-positive-check ,negative)
            :layer :b
            :doc "Original unrestricted carrier formula. Its exact closed-instance refutation and distinct stored-guard interface are in the reader refutation unit; this obligation is never discharged by that replacement.")
          fact)
         (fn2-checkpoint-reader-partition-contracts
          args (cdr specs) (cdr facts)))))))
'''


def transform(source):
    if '(local (defun fn2-checkpoint-reader-partition-contracts ' in source:
        return source
    node = rw.unique(source, PATTERN)
    args = node.items[2]
    options = node.items[3:]
    def option(key):
        return next(options[i+1] for i, n in enumerate(options) if rw.atom(n) == key)
    carriers, hints = option(':carriers'), option(':hints')
    raw = lambda n: source[n.start:n.end]
    replacement = HELPER + '''(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-check-step)
        (args (getpropc name 'formals :missing world))
        (expected-args '%s)
        (carriers '%s)
        (hints '%s)
        (hyps (fn2-columns-carrier-hyps carriers))
        (specs (fn2-columns-carrier-specs carriers))
        (facts (fn2-columns-preservation-facts name (cons name args) specs hyps hints)))
  (if (or (not (equal args expected-args))
          (not (fn2-columns-contract-carriersp carriers args
                (getpropc name 'stobjs-in nil world)
                (getpropc name 'stobjs-out nil world) world))
          (not (equal (len facts) 16)))
      (er soft 'checkpoint-reader-contract "Actual descriptor reader metadata changed.")
    (value `(progn
      ,@(fn2-checkpoint-reader-partition-contracts args specs facts)
      (in-theory (disable fn2-checkpoint-check-step)))))))

; Distinct actual-guard interface. The omitted scalar/capacity premises are
; already in the stored guard; no runtime or guard is strengthened here.
(defcolumns-guarded-contracts fn2-checkpoint-check-step
 :carriers ((fn2-fc 4 :prefix "-CHECKER") (fn2-b3 5 :prefix "-HASHER")
            (fn2-digests 8 :prefix "-DIGESTS"))
 :hints ((fn2-columns-guard-hint
    '(fn2-checkpoints fn2-checkpoint-refs fn2-checkpoint-bytes fn2-fc fn2-fc-context
      fn2-b3 fn2-fields fn2-pool fn2-digests)
    '(fn2-format-run fn2-checkpoint-decode fn2-checkpoint-capture-roots fn2-checkpoint-hash-matchesp)
    '(fn2-checkpoint-check-step) world)))''' % (raw(args), raw(carriers), raw(hints))
    return lr.write(source, [(node.start, node.end, replacement)])


def refutation_unit(source):
    """Reuse the admitted control's exact setup and actual call arguments."""
    node = rw.unique(source, '(defun-nx fn2-checkpoint-reader-scalar-domain-check ?*body)')
    body = node.items[-1]
    bindings = body.items[1].items
    setup = bindings[:next(i for i, n in enumerate(bindings) if rw.atom(n.items[0]) == 'whole-h')]
    answer = next(n for n in bindings if rw.atom(n.items[0]) == 'answer')
    call = answer.items[1]
    raw = lambda n: source[n.start:n.end]
    out = ['''; Exact live-claim refutations and CRITICAL stored-guard carrier controls.
; Production bodies/guards are unchanged. All new registry/proof events here
; require their own admission; the four original ground controls retain their
; separately recorded author PASS and do not certify the checkpoint book.
(in-package "ACL2")
(include-book "checkpoint-reader-scalar-domain-unit")
(include-book "../books/owed-discharge")
(include-book "../books/assurance-completion")
''']
    out += ['(defun-nx fn2-checkpoint-reader-refutation-arguments (which)\n (let* (' + '\n        '.join(map(raw, setup)) + '\n        (off 0) (len *fn2-format-sector-size*))\n  (list ' + ' '.join(map(raw, call.items[1:])) + ')))\n']
    out += ['''; Zero-argument teeth execute the same whole-guard/whole-original-H
; controls as the ground theorems, using logical stobj semantics throughout.
(defun-nx fn2-checkpoint-reader-guard-positive-check ()
 (fn2-checkpoint-reader-scalar-domain-check :positive))
(defthm fn2-checkpoint-reader-guard-positive-tooth
 (fn2-checkpoint-reader-guard-positive-check)
 :rule-classes nil
 :hints (("Goal" :use fn2-checkpoint-reader-positive-scalar-domain-ground
          :in-theory (e/d (fn2-checkpoint-reader-guard-positive-check)
                         (fn2-checkpoint-reader-scalar-domain-check)))))
''']
    for case in ('checker', 'hasher', 'digests'):
        out += [f'''(defun-nx fn2-checkpoint-reader-{case}-domain-removal-check ()
 (fn2-checkpoint-reader-scalar-domain-check :{case}))
(defthm fn2-checkpoint-reader-{case}-domain-removal-tooth
 (fn2-checkpoint-reader-{case}-domain-removal-check)
 :rule-classes nil
 :hints (("Goal" :use fn2-checkpoint-reader-{case}-scalar-domain-ground
          :in-theory (e/d (fn2-checkpoint-reader-{case}-domain-removal-check)
                         (fn2-checkpoint-reader-scalar-domain-check)))))
''']
    for case in ('checker', 'hasher', 'digests'):
        for facet in ('type', 'wfp'):
            old = f'fn2-checkpoint-check-step-{case}-{facet}'
            args = '\n        '.join(f'(nth {i} (fn2-checkpoint-reader-refutation-arguments :{case}))' for i in range(len(call.items)-1))
            out += [f'''
; Negation of a closed instance of THIS live original $OWED statement.
(defthm {old}-refuted-instance
 (not ({old}$owed
        {args}))
 :rule-classes nil
 :hints (("Goal"
  :use fn2-checkpoint-reader-{case}-scalar-domain-ground
  :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                    fn2-checkpoint-reader-scalar-domain-check {old}$owed)
                   (fn2-checkpoint-check-step)))))
(defsquare-refuted {old}
 {old}-refuted-instance {old}-under-guard)
''']
    out += ['''
; Register the new six CRITICAL extraction/shape contracts from the SAME
; stored-guard metadata and carrier projections as the production interface.
; Each square has exact formula identity plus whole-H positive/removal teeth.
(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-check-step)
        (args (getpropc name 'formals :missing world))
        (inputs (getpropc name 'stobjs-in nil world))
        (outputs (getpropc name 'stobjs-out nil world))
        (guard (getpropc name 'guard :missing world))
        (carriers '((fn2-fc 4 :prefix "-CHECKER")
                    (fn2-b3 5 :prefix "-HASHER")
                    (fn2-digests 8 :prefix "-DIGESTS")))
        (hyps (remove-duplicates-equal
               (append (fn2-columns-carrier-hyps carriers)
                       (fn2-columns-readonly-type-hyps args inputs nil world)
                       (list guard))))
        (specs (fn2-columns-guard-domain-specs (fn2-columns-carrier-specs carriers)))
        (facts (fn2-columns-preservation-facts name (cons name args) specs hyps nil)))
  (if (or (eq args :missing) (eq guard :missing)
          (not (fn2-columns-contract-carriersp carriers args inputs outputs world)))
      (er soft 'checkpoint-reader-critical "Actual stored-guard producer metadata changed.")
    (value (cons 'progn
     (fn2-checkpoint-reader-critical-events args specs facts))))))
''']
    # Define the recursive event assembler before its MAKE-EVENT consumer.
    helper = '''(local (defun fn2-checkpoint-reader-critical-events (args specs facts)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (let* ((fact (car facts)) (theorem (cadr fact))
         (claim (fn2-columns-sym theorem "-CLAIM"))
         (negative (cdr (assoc-equal (caddar specs)
                       '((4 . fn2-checkpoint-reader-checker-domain-removal-check)
                         (5 . fn2-checkpoint-reader-hasher-domain-removal-check)
                         (8 . fn2-checkpoint-reader-digests-domain-removal-check))))))
   (append
    `((defthm-owed ,claim ,args ,(caddr fact)
       :teeth (fn2-checkpoint-reader-guard-positive-check ,negative)
       :layer :b :boundary :extraction
       :doc "Actual CHECK-STEP stored-guard carrier theorem, with whole-domain positive and domain-removal logical controls. Not descriptor authentication or boot readiness.")
      (fn2-owed-discharge ,claim ,theorem))
    (fn2-checkpoint-reader-critical-events args (cdr specs) (cdr facts)))))))
'''
    out.insert(-1, helper)
    # Source metadata determines the six cases; the registry independently
    # checks exact live statement identity and closedness at ACL2 admission.
    names = [f'fn2-checkpoint-check-step-{c}-{f}' for c in ('checker','hasher','digests') for f in ('type','wfp')]
    out += ['''
; Refutation leaves originals unfinished. No replacement proves an original.
(assert-event
 (let* ((names '%s)
        (rows (fn2-decl-rows :square (w state))))
  (and (subsetp-eq names (fn2-owed-names (w state)))
       (equal (nth 2 (fn2-square-counts (fn2-checkpoint-reader-original-rows names rows))) 0))))
''' % ('(' + ' '.join(names) + ')')]
    rowhelper = '''(local (defun fn2-checkpoint-reader-original-rows (names rows)
 (declare (xargs :verify-guards nil))
 (if (atom names) nil
  (cons (assoc-eq (car names) rows)
        (fn2-checkpoint-reader-original-rows (cdr names) rows)))))
'''
    out.insert(-1, rowhelper)
    out += ['''
; Bind predicate conclusions directly in the ONE canonical evidence store.
; All indices/cases are quoted because these are translated closed terms.
(local (defun fn2-checkpoint-reader-evidence-bindings (args which i)
 (declare (xargs :verify-guards nil))
 (if (atom args) nil
  (cons (list (car args)
              `(nth ',i (fn2-checkpoint-reader-refutation-arguments ',which)))
        (fn2-checkpoint-reader-evidence-bindings (cdr args) which (+ 1 i))))))
(local (defun fn2-checkpoint-reader-evidence-hints (ground)
 (declare (xargs :verify-guards nil))
 `(("Goal" :use ,ground
    :in-theory (e/d (fn2-checkpoint-reader-refutation-arguments
                      fn2-checkpoint-reader-scalar-domain-check)
                     (fn2-checkpoint-check-step))))))
(local (defun fn2-checkpoint-reader-evidence-events (specs facts args guard world)
 (declare (xargs :verify-guards nil))
 (if (atom specs) nil
  (let* ((claim (fn2-columns-sym (cadar facts) "-CLAIM"))
         (case (cdr (assoc-equal (caddar specs)
                                '((4 . :checker) (5 . :hasher) (8 . :digests)))))
         (ground (cdr (assoc-eq case
                    '((:checker . fn2-checkpoint-reader-checker-scalar-domain-ground)
                      (:hasher . fn2-checkpoint-reader-hasher-scalar-domain-ground)
                      (:digests . fn2-checkpoint-reader-digests-scalar-domain-ground)))))
         (row (fn2-decl-row (list :square claim) world))
         (statement (fn2-decl-get :statement row))
         (formula (fn2-decl-statement-body statement world)))
   (mv-let (hyp conclusion) (fn2-evidence-parts formula)
    (declare (ignore conclusion))
    (mv-let (count remaining) (fn2-evidence-hypothesis-cut hyp guard)
     (declare (ignore remaining))
     (if (not (and case ground row (equal count 1)
                    (equal args (fn2-decl-get :vars row))))
         (er hard 'checkpoint-reader-evidence
             "Stored guard must occur exactly once in actual live claim ~x0." claim)
       (cons
        (fn2-square-predicate-evidence-events-with-hints
         claim (fn2-checkpoint-reader-evidence-bindings args :positive 0)
         (list :kind :hypothesis-removal :remove guard
               :bindings (fn2-checkpoint-reader-evidence-bindings args case 0))
         (fn2-checkpoint-reader-evidence-hints
          'fn2-checkpoint-reader-positive-scalar-domain-ground)
         (fn2-checkpoint-reader-evidence-hints ground) nil world)
        (cons `(fn2-assert-square-evidence ,claim)
         (fn2-checkpoint-reader-evidence-events (cdr specs) (cdr facts) args guard world))))))))))
(make-event
 (let* ((world (w state)) (name 'fn2-checkpoint-check-step)
        (args (getpropc name 'formals :missing world))
        (guard (getpropc name 'guard :missing world))
        (carriers '((fn2-fc 4 :prefix "-CHECKER")
                    (fn2-b3 5 :prefix "-HASHER")
                    (fn2-digests 8 :prefix "-DIGESTS")))
        (specs (fn2-columns-guard-domain-specs (fn2-columns-carrier-specs carriers)))
        (facts (fn2-columns-preservation-facts name (cons name args) specs nil nil)))
  (if (or (eq args :missing) (eq guard :missing))
      (er soft 'checkpoint-reader-evidence "No actual reader guard/signature.")
    (value (cons 'progn
            (fn2-checkpoint-reader-evidence-events specs facts args guard world))))))
''']
    return '\n'.join(out)


def boot_bridge(source):
    node = rw.unique(source, '(defun fn2-boot-checkpoint-descriptor-pool ?*body)')
    if 'fn2-boot-checkpoint-descriptor-pool-guarded-bridge' in source:
        return source
    xargs = next(n for n in rw.walk(node) if n.items and rw.atom(n.items[0]) == 'xargs')
    at = next(i for i, n in enumerate(xargs.items) if rw.atom(n) == ':guard')
    insertion = xargs.items[at].start
    hint = ''':guard-hints ((fn2-columns-call-guard-hint
     'fn2-boot-checkpoint-descriptor-pool
     '(fn2-checkpoint-check-step fn2-checkpoint-restore-load-hash) nil world))
  '''
    contracts = '''
; fn2-boot-checkpoint-descriptor-pool-guarded-bridge: the actual boot face
; checks row/capacity, loads its retained candidate hash and writes context
; before CHECK-STEP. Consume that producer's distinct stored-guard facts;
; the six false unrestricted originals are never used as caller contracts.
(defcolumns-guarded-contracts fn2-boot-checkpoint-descriptor-pool
 :carriers ((fn2-fc 4 :prefix "-CHECKER") (fn2-b3 6 :prefix "-HASHER")
            (fn2-digests 9 :prefix "-DIGESTS"))
 :hints ((fn2-columns-call-guard-hint
    'fn2-boot-checkpoint-descriptor-pool
    '(fn2-checkpoint-check-step fn2-checkpoint-restore-load-hash)
    '(fn2-boot-checkpoint-descriptor-pool) world)))
'''
    include = source.index('(fn2-book-layer :b)')
    return lr.write(source, [(include, include, '(local (include-book "columns-call-guards"))\n'),
                             (insertion, insertion, hint), (node.end, node.end, contracts)])


if __name__ == '__main__':
    path = ROOT / 'books/checkpoint.lisp'
    path.write_text(transform(path.read_text()))
    fixture = ROOT / 'tests/checkpoint-reader-scalar-domain-unit.lisp'
    (ROOT / 'tests/checkpoint-reader-refutation-unit.lisp').write_text(refutation_unit(fixture.read_text()))
    boot = ROOT / 'books/boot.lisp'
    boot.write_text(boot_bridge(boot.read_text()))
