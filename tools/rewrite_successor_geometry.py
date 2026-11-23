#!/usr/bin/env python3
"""Scoped C successor workspace repair; dimensions come from ACL2 declarations."""
from pathlib import Path
import sys,json
sys.path.insert(0,str(Path(__file__).resolve().parent))
from lisp_rewrite import parse,match,write
if '(include-book "successor-schema-geometry")' in Path('books/machines-c.lisp').read_text():
 print('successor geometry: unchanged')
 raise SystemExit(0)
Path('books/successor-workspace-geometry.lisp').write_text('; Pure layout arithmetic shared by allocation admission and C\'s static schema\n; inventory. A guard reservation is not an entry write footprint.\n(in-package "ACL2")\n(include-book "format-base")\n(fn2-book-layer :b)\n(defun fn2-successor-block-fields (fields values)\n (declare (xargs :guard (and (natp fields) (natp values))))\n (+ (* 3 (nfix fields)) (nfix values) 1))\n(defun fn2-successor-required-fields (fields values slots entry-guard reader-fields)\n (declare (xargs :guard (and (natp fields) (natp values) (natp slots) (natp entry-guard) (natp reader-fields))))\n (let ((block (fn2-successor-block-fields fields values)))\n  (max (+ (* (nfix slots) block) 4 (nfix entry-guard) (nfix reader-fields))\n       (+ (* (nfix (- (nfix slots) 1)) block) (nfix entry-guard)))))\n(defun fn2-successor-scratch-bytes (octets)\n (declare (xargs :guard (natp octets)))\n (* *fn2-format-sector-size* (max 1 (ceiling (nfix octets) *fn2-format-sector-size*))))\n(defthm fn2-successor-block-fields-covers-regions\n (implies (and (natp fields) (natp values))\n  (and (<= fields (* 2 fields))\n       (<= (* 2 fields) (* 3 fields))\n       (< (+ (* 3 fields) values) (fn2-successor-block-fields fields values))))\n :hints (("Goal" :in-theory (enable fn2-successor-block-fields))))\n')
p=Path('books/machines-c-successor.lisp');src=p.read_text()
names=['fn2-succ-octets-total']
move=['*fn2-succ-entry*','*fn2-succ-raw*','*fn2-succ-eval*','*fn2-succ-res*','*fn2-succ-fresh*','*fn2-succ-fields-max*','*fn2-succ-values-max*']
edits=[]
# Current-root owns this old constant in successor; cold owns it in its
# separate identity-workspace provider (the named cold follow-up removes it).
for h in match('(defconst *fn2-idc-scratch-bytes* ?*body)',parse(src).forms,deep=False):
 edits.append((h.start,h.end,''))
for n in move:
 h=match('(defconst '+n+' ?*body)',parse(src).forms,deep=False)[0];edits.append((h.start,h.end,''))
h=match('(defun fn2-succ-octets-total ?*body)',parse(src).forms,deep=False)[0]
octets=src[h.start:h.end];edits.append((h.start,h.end,''))
src=write(src,edits)
src=src.replace('(or (not (fn2-run-layout-fold-p sid)) (<= (- nf (fn2-run-layout-keys sid)) *fn2-succ-values-max*))','(<= (- nf (fn2-run-layout-keys sid)) *fn2-succ-values-max*)')
p.write_text(src)
geometry='; Schema inventory is evaluated once by ACL2 at declaration time. No served\n; operation scans declarations, and no article-specific field limit is used.\n(in-package "ACL2")\n(include-book "runs-served")\n(include-book "successor-workspace-geometry")\n(fn2-book-layer :c)\n(defun fn2-succ-octets-total (sid f n)\n (declare (xargs :verify-guards nil :measure (nfix (- (nfix n) (nfix f)))))\n (if (<= (nfix n) (nfix f)) 0 (+ (nfix (fn2-run-layout-octets-max sid f)) (fn2-succ-octets-total sid (+ 1 (nfix f)) n))))\n(defun fn2-successor-fold-args-max (sid kinds)\n (declare (xargs :verify-guards nil))\n (if (atom kinds) 0\n  (max (nfix (fn2-fold-arity sid (car kinds))) (fn2-successor-fold-args-max sid (cdr kinds)))))\n(defun fn2-successor-schema-bounds (ids)\n (declare (xargs :verify-guards nil))\n (if (atom ids) \'(0 0 0)\n  (let* ((sid (car ids)) (nf (nfix (fn2-run-layout-fields sid 0)))\n         (nk (nfix (fn2-run-layout-keys sid)))\n         (rest (fn2-successor-schema-bounds (cdr ids))))\n   (list (max nf (fn2-successor-fold-args-max sid *fn2-run-fold-kinds*) (nfix (car rest)))\n         (max (nfix (- nf nk)) (nfix (cadr rest)))\n         (max (fn2-succ-octets-total sid 0 nf) (nfix (caddr rest)))))))\n(make-event\n (let ((bounds (fn2-successor-schema-bounds *fn2-run-assembled-ids*)))\n  (value `(progn\n    (defconst *fn2-succ-fields-max* ,(car bounds))\n    (defconst *fn2-succ-values-max* ,(cadr bounds))\n    (defconst *fn2-succ-octets-max* ,(caddr bounds))))))\n(defconst *fn2-succ-entry* 0)\n(defconst *fn2-succ-raw* *fn2-succ-fields-max*)\n(defconst *fn2-succ-eval* (+ *fn2-succ-raw* *fn2-succ-fields-max*))\n(defconst *fn2-succ-res* (+ *fn2-succ-eval* *fn2-succ-fields-max*))\n(defconst *fn2-succ-fresh* (+ *fn2-succ-res* *fn2-succ-values-max*))\n(defconst *fn2-succ-block* (fn2-successor-block-fields *fn2-succ-fields-max* *fn2-succ-values-max*))\n(defconst *fn2-idc-scratch-bytes* (fn2-successor-scratch-bytes *fn2-succ-octets-max*))\n; Bind cost propagation is a separate actual-call audit, not an inferred\n; bound from per-entry scratch size. This book changes no byte-cost claim.\n(assert-event\n (and (<= *fn2-succ-fields-max* 32)\n      (<= *fn2-succ-values-max* *fn2-succ-fields-max*)\n      (< *fn2-succ-fresh* 256)\n      (<= *fn2-succ-fields-max* *fn2-succ-raw*)\n      (<= (+ *fn2-succ-raw* *fn2-succ-fields-max*) *fn2-succ-eval*)\n      (<= (+ *fn2-succ-eval* *fn2-succ-fields-max*) *fn2-succ-res*)\n      (<= (+ *fn2-succ-res* *fn2-succ-values-max*) *fn2-succ-fresh*)\n      (< *fn2-succ-fresh* *fn2-succ-block*)\n      (<= *fn2-succ-octets-max* *fn2-idc-scratch-bytes*)))\n'
Path('books/successor-schema-geometry.lisp').write_text(geometry)
p=Path('books/machines-c.lisp');src=p.read_text();src=src.replace('(include-book "machines-b")','(include-book "machines-b")\n(include-book "successor-schema-geometry")',1)
h=match('(defconst *fn2-succ-block* ?*body)',parse(src).forms,deep=False)[0];src=write(src,[(h.start,h.end,'')])
needle='(defconst *fn2-idc-rb* (+ *fn2-idc-eb* *fn2-run-entry-rows*))';assert needle in src
src=src.replace(needle,needle+'''
(defconst *fn2-idc-required-fields*
 (fn2-successor-required-fields *fn2-succ-fields-max* *fn2-succ-values-max*
  *fn2-succ-slots* *fn2-run-entry-rows* *fn2-run-reader-fields*))
(assert-event (<= *fn2-idc-required-fields* *fn2-idc-stride*))''')
p.write_text(src)

# Canonical comments follow the same generated geometry on both source variants.
p=Path('books/machines-c.lisp');s=p.read_text().replace('; *fn2-b-txn-field-rows*-row stripe ending','; *fn2-b-txn-field-rows*-row supported stripe ending');a=s.index('; a stripe (C-STRIPE)');b=s.index('(defconst *fn2-idc-stride*',a);s=s[:a]+"; a stripe (C-STRIPE), the successor's declared write slots occupy disjoint\n; blocks derived from the assembled schema inventory. The exact lookup follows\n; at *fn2-idc-ident*: its query begins at +4, then the shared run reader.\n"+s[b:];p.write_text(s)
p=Path('books/machines-c-successor.lisp');s=p.read_text();a=s.index('; The bind scratch takes');b=s.index('(assert-event (<= (+ *fn2-succ-res*',a);s=s[:a]+"; The bind scratch takes one slot's octets at a time: an entry's octet\n; fields in field order from 0; its capacity comes from the same inventory.\n\n; C-STRIPE: ENTRY, RAW args, EVAL args, RES values and FRESH occupy\n; disjoint declaration-derived regions. The generic run decoder's 80-row guard\n; is a table-tail reservation; its actual entry writes are the schema fields.\n; successor-schema-geometry owns every offset and capacity.\n"+s[b:];p.write_text(s)
p=Path('books/machines-c-successor.lisp');s=p.read_text().replace(';; Every assembled schema fits a slot: at most 12 entry fields and, for a\n;; fold, 8 value fields and 12 args per event kind; its octet fields fit the\n;; bind scratch together.',';; Every assembled schema and fold fits the inventory-derived slot; all\n;; readable value fields fit RES, and its octets fit the actual scratch class.');p.write_text(s)
