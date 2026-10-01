#!/usr/bin/env python3
"""Emit the build-only ACL2 driver for selected genuine source producer roots.

This performs no resource arithmetic or readiness decision. ACL2 checks each
actual world ABI and evaluates its four-MV source result into an immutable
constant. Phase/refinement/cost evidence remains the protocol source's duty;
world metadata alone never qualifies an operation. The driver is not served.
"""
import argparse
import json
from pathlib import Path
import re


def driver(rows):
    seen = set()
    includes, terms, checks, body_terms, role_terms = [], [], [], [], []
    for row in rows:
        if not {"kind", "book", "producer"} <= set(row) or set(row) - {"kind", "book", "producer", "body_producer", "executor_role_producer"}:
            raise ValueError("selected root needs kind/book/producer and optional actual body_producer")
        kind, book, source = row["kind"], row["book"], row["producer"]
        if not isinstance(kind, str) or not re.fullmatch(r":[a-z][a-z0-9-]*", kind):
            raise ValueError("invalid operation kind")
        if kind in seen:
            raise ValueError("duplicate operation kind")
        seen.add(kind)
        if not isinstance(book, str) or not re.fullmatch(r"[a-z][a-z0-9/-]*", book) or ".." in book:
            raise ValueError("invalid selected source book")
        if not isinstance(source, str) or not re.fullmatch(r"fn-[a-z][a-z0-9-]*", source):
            raise ValueError("invalid actual source function")
        if source == "fn-runtime-operation-compiled-source":
            raise ValueError("compiled readout cannot be its own source")
        include = '(include-book "' + book + '")'
        if include not in includes:
            includes.append(include)
        checks.append("""(and (equal (getpropc '%s 'formals :missing (w state)) '(kind))
             (equal (getpropc '%s 'stobjs-in :missing (w state)) '(nil))
             (equal (getpropc '%s 'stobjs-out :missing (w state)) '(nil nil nil nil))
             (equal (getpropc '%s 'symbol-class :missing (w state)) :common-lisp-compliant))""" % ((source,) * 4))
        body = row.get("body_producer")
        if body is not None:
            if not isinstance(body, str) or not re.fullmatch(r"fn-[a-z][a-z0-9-]*", body):
                raise ValueError("invalid actual body source function")
            if body in {"fn-runtime-operation-compiled-body-cost", "fn-roc-selected-body-cost"}:
                raise ValueError("compiled body dispatcher cannot be its own source")
            checks.append("""(and (equal (getpropc '%s 'formals :missing (w state)) '(kind request cached))
             (equal (getpropc '%s 'stobjs-in :missing (w state)) '(nil nil nil))
             (equal (getpropc '%s 'stobjs-out :missing (w state)) '(nil nil))
             (equal (getpropc '%s 'symbol-class :missing (w state)) :common-lisp-compliant))""" % ((body,) * 4))
            body_terms.append("(%s (%s kind request cached))" % (kind, body))
        role_source = row.get("executor_role_producer")
        if role_source is not None:
            if not isinstance(role_source, str) or not re.fullmatch(r"fn-[a-z][a-z0-9-]*", role_source):
                raise ValueError("invalid actual executor-role source function")
            checks.append("""(and (equal (getpropc '%s 'formals :missing (w state)) '(kind))
             (equal (getpropc '%s 'stobjs-in :missing (w state)) '(nil))
             (equal (getpropc '%s 'stobjs-out :missing (w state)) '(nil nil))
             (equal (getpropc '%s 'symbol-class :missing (w state)) :common-lisp-compliant))""" % ((role_source,) * 4))
            role_terms.append("""(if (fn-roc-positive-entryp
                       (fn-roc-entry %s *fn-runtime-operation-compiled-table*))
                 (mv-let (status role) (%s %s)
                   (if (and (eq status :compiled-operation-source) (symbolp role) role)
                       (list %s role) nil)) nil)""" % (kind, role_source, kind, kind))
        terms.append("(mv-let (status family roles prs) (%s %s)\n       (list %s status family roles prs))" % (source, kind, kind))
    check = "(and " + "\n        ".join(checks) + ")" if checks else "t"
    table = "(list " + "\n      ".join(terms) + ")" if terms else "nil"
    roles = "(list " + "\n      ".join(role_terms) + ")" if role_terms else "nil"
    body_dispatch = """(defun fn-roc-selected-body-cost (kind request cached)
        (declare (xargs :guard t))
        (if (and *fn-runtime-operation-compiled-binding*
                 (fn-roc-positive-entryp
                   (fn-roc-entry kind *fn-runtime-operation-compiled-table*)))
            (case kind %s (otherwise (mv :runtime-operation-unavailable nil)))
          (mv :runtime-operation-unavailable nil)))""" % " ".join(body_terms)
    if not body_terms:
        body_dispatch = """(defun fn-roc-selected-body-cost (kind request cached)
        (declare (ignore kind request cached) (xargs :guard t))
        (mv :runtime-operation-unavailable nil))"""
    return """; Generated build-only driver: no host-computed charge or qualified flag.
(in-package "ACL2")
(include-book "runtime-operation-source-assembly")
%s
(make-event
 (if %s
     (value '(progn
       (defconst *fn-runtime-operation-compiled-table* %s)
       (defconst *fn-runtime-operation-compiled-binding*
        (fn-roc-compiled-binding *fn-runtime-operation-compiled-table*))
       (defconst *fn-runtime-operation-compiled-executor-rows* %s)
       (defconst *fn-runtime-operation-compiled-kinds*
        (if *fn-runtime-operation-compiled-binding*
            (fn-roc-executor-kinds *fn-runtime-operation-compiled-executor-rows*) nil))
       (defconst *fn-runtime-operation-compiled-slots*
        (fn-roc-operation-slots *fn-runtime-operation-compiled-executor-rows*
         (fn-roc-slot-rows *fn-runtime-operation-compiled-kinds* 0)))
       %s))
   (er soft 'runtime-operation-source-compile
       "Selected actual producer is absent, unguarded, impure, or has a different ABI.")))
""" % ("\n".join(includes), check, table, roles, body_dispatch)


def main():
    p = argparse.ArgumentParser(description=__doc__)
    p.add_argument("selected_roots", type=Path)
    p.add_argument("output", type=Path)
    a = p.parse_args()
    rows = json.loads(a.selected_roots.read_text())
    if not isinstance(rows, list):
        p.error("selected roots must be a list")
    try:
        text = driver(rows)
    except ValueError as e:
        p.error(str(e))
    a.output.write_text(text)


if __name__ == "__main__":
    main()
