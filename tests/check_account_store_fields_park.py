"""Actual frozen C preparation/history/park composition; UNFUNDED parents.

Run with --tree the integration tree after Fields14 lands. Before integration,
--frozen-preparation selects precisely 52ef6a642's preparation source.
--continuation selects a review-only corrected source for a fix demonstration.
"""
import argparse
import ast
import os
from pathlib import Path
import runpy
import subprocess
import sys
import tempfile

p = argparse.ArgumentParser()
p.add_argument('--tree', type=Path, required=True)
p.add_argument('--frozen-preparation', action='store_true')
p.add_argument('--continuation', type=Path)
a = p.parse_args()
sys.path.insert(0, str(a.tree))
from tools.commit_map import resolve
ns = runpy.run_path(str(a.tree / 'tests/test_native_account_adoption_transport.py'))
module = ast.parse((a.tree / 'tests/test_native_account_adoption_transport.py').read_text())
test = next(x for x in module.body if isinstance(x, ast.FunctionDef) and x.name == 'test_actual_configuration_claim_parks_and_rebinds_without_issue')
program = ast.literal_eval(test.body[1].value)
program += '\n(defun true-listp (x) (or (null x) (and (consp x) (true-listp (cdr x)))))\n(defun len (x) (length x))\n'

def named(path, prefix):
    if path == 'host/account-config-preparation-host.lisp' and a.frozen_preparation:
        text = subprocess.check_output(['git', 'show', resolve('52ef6a642', a.tree) + ':' + path], cwd=a.tree, text=True)
    elif path == 'host/account-config-continuation-host.lisp' and a.continuation:
        text = a.continuation.read_text()
    else:
        text = (a.tree / path).read_text()
    return next(text[x:y] for x, y in ns['spans'](text) if text[x:y].startswith(prefix))

forms = [
 ('books/consumer-position-fields.lisp', '(defun fn-cp-nth '),
 ('books/page-read-ledger.lisp', '(defun fn-prl-nth '),
 ('books/admission-preallocation-resources.lisp', '(defun fn-apr-widthp '),
 ('books/account-adoption-input-source.lisp', '(defun fn-cado-widthp '),
 ('books/account-adoption-input-source.lisp', '(defun fn-cado-receipt-coordinatep '),
 ('books/account-adoption-input-source.lisp', '(defun fn-cado-source-keyp '),
 ('books/account-adoption-turn.lisp', '(defun fn-act-livep '),
 ('books/account-adoption-turn-continuation.lisp', '(defun fn-act-suspend '),
 ('host/account-adoption-turn-host.lisp', '(defun fn-owner-account-turn-current-bodyp\n'),
 ('books/history-config-journal-state.lisp', '(defun fn-owner-history-config-journal '),
 ('books/account-config-history-cursor.lisp', '(defun fn-ach-state '),
 ('books/account-config-history-cursor.lisp', '(defun fn-ach-begin '),
 ('books/account-config-history-cursor.lisp', '(defun fn-ach-tick '),
 ('host/account-config-preparation-host.lisp', '(defun fn-owner-account-config-preparation-state '),
 ('host/account-config-preparation-host.lisp', '(defun fn-owner-account-config-preparation-step '),
 ('host/account-config-continuation-host.lisp', '(defun fn-owner-account-config-continuation-currentp '),
 ('host/account-config-continuation-host.lisp', '(defun fn-owner-account-config-suspended-currentp '),
 ('host/account-config-continuation-host.lisp', '(defun fn-owner-account-config-suspend-current\n'),
 ('host/account-adoption-return-host.lisp', '(defun fn-owner-account-turn-return-current\n'),
]
for path, prefix in forms:
    program += ns['cl_form'](named(path, prefix)) + '\n'
program += '''
(let* ((token '(:account-preparation-turn 7 3 4))
       (id '(:account-operation :candidate 9 10))
       (key (list :account-adoption-source token 3 4 (make-list 32 :initial-element 0) 10))
       (oldrequest (list :original-input)) (oldjob (list :original-job))
       (intent (list :account-turn-reservation :original-ledger :proposed-ledger
                     :original-complete-resources 2 17))
       (row (list :account-turn token :reserved '(8 0 0 0 1)
                  :operation-select key oldrequest oldjob nil intent))
       (holder (list :account-adoption-operation id key '(:configure :marker)
                     oldjob 3 4 8 9 10 :namespace 12 oldrequest token))
       (base (list :history-config-base id :original-store :original-config
                   :canonical :view :posting :obligation))
       (prep (list :account-config-preparation id token :full8 :record base :metadata
                   :history (fn-ach-begin nil :actual-record) :generation-cursor
                   4 5 :next-node nil))
       (lease (list :history-config-source id token :parent 3 8 4 :coordinate :record :acquired))
       (state (list (cons 'current row) (cons 'holder holder) (cons 'lease lease)
                    (cons 'fn-owner-account-config-preparation prep)
                    (cons 'fn-owner-history-config-base base)))
       (pool (list :original-pool)) (slots (list :actual-slots)))
 ;; Execute the actual cursor and actual high preparation, not a phase setter.
 (dotimes (i 2)
  (multiple-value-bind (word next) (fn-owner-account-config-preparation-step state)
   (assert (eq word :yield)) (setf state next)))
 (let ((completed (fn-owner-account-config-preparation-state state)))
  (assert (eq (nth 7 completed) :store-fields))
  (assert (equal (nth 4 (nth 8 completed)) '(:actual-record)))
  (multiple-value-bind (word next-pool parked)
    (fn-owner-account-turn-return-current 2 17 slots pool state)
   (assert (eq word :account-turn-retained))
   (assert (eq next-pool pool))
   (let ((saved (fn-owner-account-turn-current parked)))
    (assert (eq (third saved) :suspended))
    (dolist (i '(1 3 4 5 6 7 9)) (assert (eq (nth i saved) (nth i row))))
    (assert (eq (nth 4 (nth 8 saved)) completed)))))
 ;; An allocation escape at StoreFields intent must still refuse parking.
 (let* ((badprep (update-nth 7 :store-fields-intent (fn-owner-account-config-preparation-state state)))
        (bad (f-put-global 'fn-owner-account-config-preparation badprep state)))
  (multiple-value-bind (word next-pool next-state)
    (fn-owner-account-turn-return-current 2 17 slots pool bad)
   (assert (eq word :account-return-pending))
   (assert (and (eq next-pool pool) (eq next-state bad))))))
(format t "ACTUAL_HISTORY_TO_STORE_FIELDS_PARK_PASS; synthetic UNFUNDED parents.~%")
'''
with tempfile.TemporaryDirectory(prefix='fn-closeout-account-') as d:
    path = Path(d) / 'regression.lisp'
    path.write_text(program)
    r = subprocess.run(['sbcl', '--noinform', '--script', str(path)], text=True, capture_output=True, timeout=30)
    print(r.stdout + r.stderr)
    raise SystemExit(r.returncode)
