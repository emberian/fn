#!/usr/bin/env python3
"""Install the requested ground PIN-VALUE teeth in the rooted test book."""
from pathlib import Path
import sys
sys.path.insert(0,str(Path(__file__).resolve().parents[2]/'tools'))
import lisp_rewrite as lr
root=Path(__file__).resolve().parents[2]
p=root/'tests/acl2/owner-config-tests.lisp'
t=p.read_text()
assert '; PIN-VALUE profile teeth' not in t
source=(root/'books/owner-config.lisp').read_text()
node=lr.match(None,lr.parse(source).forms,head='defun',name='fn-ocfg-open')[0].node
mutant=source[node.start:node.end].replace('(defun fn-ocfg-open ', '(defun ocfg-pv-cfg-only-open ')
mutant=mutant.replace('(declare (xargs :guard t))','(declare (xargs :guard t) (ignore profile))')
assert '(cons (fn-ocfg-config oc) profile)' in mutant
mutant=mutant.replace('(cons (fn-ocfg-config oc) profile)','(fn-ocfg-config oc)')
teeth='''
; -----------------------------------------------------------------------------
; PIN-VALUE profile teeth (ruling B): an open pins its own profile, and a
; configuration move preserves the two different profiles already held.
(include-book "../../books/owner-reclaim-pass")

(defconst *ocfg-pv-p1* '(:profile :first))
(defconst *ocfg-pv-p2* '(:profile :second))
(assert-event (not (equal *ocfg-pv-p1* *ocfg-pv-p2*)))

; The old bare-CFG table value is rejected, even though CFG itself is valid.
(assert-event
 (and (fn-cfgp *ocfg-t-g1*)
      (not (fn-ocfg-pins-okp (list (cons 0 *ocfg-t-g1*))))))

; The whole antecedent: a valid starting state, free ID 0, and an accepted
; open with an actual connection and a pin at that ID.
(defconst *ocfg-pv-first* (cdr (fn-ocfg-open *ocfg-t-0* nil *ocfg-pv-p1*)))
(assert-event
 (and (fn-ocfg-statep *ocfg-t-0*)
      (equal (fn-own-next-id (fn-ocfg-owner *ocfg-t-0*)) 0)
      (not (fn-ocfg-pin-find 0 (fn-ocfg-pins *ocfg-t-0*)))
      (not (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-t-0*))))
      (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-pv-first*)))
      (fn-ocfg-statep *ocfg-pv-first*)
      (equal (fn-ocfg-conn-profile *ocfg-pv-first* 0) *ocfg-pv-p1*)
      (equal (fn-ocfg-conn-config *ocfg-pv-first* 0) (fn-ocfg-config *ocfg-t-0*))))

; Exact open mutant: only the pin-add value differs; PROFILE is dropped.
'''+mutant+'''
(defconst *ocfg-pv-mutant* (cdr (ocfg-pv-cfg-only-open *ocfg-t-0* nil *ocfg-pv-p1*)))
(assert-event
 (and (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-pv-mutant*)))
      (not (and (equal (fn-ocfg-conn-profile *ocfg-pv-mutant* 0) *ocfg-pv-p1*)
                (equal (fn-ocfg-conn-config *ocfg-pv-mutant* 0)
                       (fn-ocfg-config *ocfg-t-0*))))))
(local
 (must-fail-checked
  (assert-event
   (and (equal (fn-ocfg-conn-profile *ocfg-pv-mutant* 0) *ocfg-pv-p1*)
        (equal (fn-ocfg-conn-config *ocfg-pv-mutant* 0)
               (fn-ocfg-config *ocfg-t-0*))))))

; Open ID 1 under a new live configuration and a different profile.
(defconst *ocfg-pv-published*
 (fn-ocfg-make (fn-ocfg-owner *ocfg-pv-first*) *ocfg-t-g2*
               (fn-ocfg-pins *ocfg-pv-first*) nil))
(defconst *ocfg-pv-two* (cdr (fn-ocfg-open *ocfg-pv-published* nil *ocfg-pv-p2*)))
(assert-event
 (and (fn-ocfg-statep *ocfg-pv-two*)
      (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-pv-two*)))
      (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *ocfg-pv-two*)))
      (equal (fn-ocfg-conn-profile *ocfg-pv-two* 0) *ocfg-pv-p1*)
      (equal (fn-ocfg-conn-profile *ocfg-pv-two* 1) *ocfg-pv-p2*)
      (equal (fn-ocfg-conn-config *ocfg-pv-two* 0) *ocfg-t-g1*)
      (equal (fn-ocfg-conn-config *ocfg-pv-two* 1) *ocfg-t-g2*)))

(defconst *ocfg-pv-advanced* (fn-ocfg-advance *ocfg-pv-two* 0))
(assert-event
 (and (equal (car (fn-own-advance-result (fn-ocfg-owner *ocfg-pv-two*) 0)) :advanced)
      (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-pv-advanced*)))
      (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *ocfg-pv-advanced*)))
      (equal (fn-ocfg-conn-config *ocfg-pv-advanced* 0) *ocfg-t-g2*)
      (equal (fn-ocfg-conn-profile *ocfg-pv-advanced* 0) *ocfg-pv-p1*)
      (equal (fn-ocfg-conn-profile *ocfg-pv-advanced* 1) *ocfg-pv-p2*)))

; A rebuild with the other configuration makes the swap move both pins.
(defconst *ocfg-pv-swapped*
 (fn-orcp-swapped-ocfg *ocfg-pv-advanced* *ocfg-t-0*))
(assert-event
 (and (fn-own-find-conn 0 (fn-own-conns (fn-ocfg-owner *ocfg-pv-swapped*)))
      (fn-own-find-conn 1 (fn-own-conns (fn-ocfg-owner *ocfg-pv-swapped*)))
      (equal (fn-ocfg-conn-config *ocfg-pv-swapped* 0) *ocfg-t-g1*)
      (equal (fn-ocfg-conn-config *ocfg-pv-swapped* 1) *ocfg-t-g1*)
      (equal (fn-ocfg-conn-profile *ocfg-pv-swapped* 0) *ocfg-pv-p1*)
      (equal (fn-ocfg-conn-profile *ocfg-pv-swapped* 1) *ocfg-pv-p2*)))
'''
p.write_text(t+teeth)
print('added PIN-VALUE teeth and exact cfg-only mutant')
