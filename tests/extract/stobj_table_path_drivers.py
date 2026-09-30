"""Generate representation-only graph fixtures; compare complete stock observations.
No admission/publication or funded-builder claim follows from these fixtures.
"""
import json
import sys
from pathlib import Path
sys.path.insert(0, str(Path(__file__).resolve().parents[2] / 'tools/extract'))
import cl
import chicken


def generate(golds, output, definitions, runtime):
    observations = {}
    for line in Path(golds).read_text().splitlines():
        label, value = line.split('>>', 1)[1].split(' ', 1)
        observations[label] = json.loads(value)
    c = ['(defpackage "ACL2" (:use "COMMON-LISP"))', '(defpackage "ACL2_INVISIBLE" (:use))', '(defpackage "ACL2_*1*_ACL2" (:use))', f'(load "{runtime}")', f'(load "{definitions}")', '(in-package "ACL2")', '(defvar node (create-fn-ibp-node))']
    s = ['(define node (|f:ACL2::CREATE-FN-IBP-NODE|))']
    def call(name, *args):
        return '(' + name.lower() + ' ' + ' '.join(map(str,args)) + ')', '(|f:ACL2::' + name.upper() + '| ' + ' '.join(map(str,args)) + ')'
    def install(branch, id, tag, encoded):
        # Fixed literal paths, deliberately no host copy of the slot traversal.
        parent='node'
        for ordinal, key in enumerate(branch):
            var='child'+str(ordinal)
            c.append(f'(defparameter {var} (create-{key}))')
            s.append(f'(define {var} (|f:ACL2::CREATE-{key.upper()}|))')
            c.append(f"(fn-ibp-node-children-put '{key} {var} {parent})")
            s.append(f"(|f:ACL2::FN-IBP-NODE-CHILDREN-PUT| '|ACL2::{key.upper()}| {var} {parent})")
            parent=var
        c.extend(['(defparameter page (create-fn-ibp-table-page))', f'(assert (eq (fn-ibp-table-initialize {id} 3 page) :initialized))', f'(fn-ibp-table-set 0 {tag} page)', f'(fn-ibp-table-set 1024 {encoded} page)', f'(assert (eq (fn-ibp-table-seal {id} 3 page) :sealed))', f"(fn-ibp-node-children-put 'fn-ibp-table-page page {parent})"])
        s.extend(['(define page (|f:ACL2::CREATE-FN-IBP-TABLE-PAGE|))', f"(call-with-values (lambda () (|f:ACL2::FN-IBP-TABLE-INITIALIZE| {id} 3 page)) (lambda (status page) (unless (eq? status '|KEYWORD::INITIALIZED|) (error \"initialize\"))))", f'(|f:ACL2::FN-IBP-TABLE-SET| 0 {tag} page)', f'(|f:ACL2::FN-IBP-TABLE-SET| 1024 {encoded} page)', f"(call-with-values (lambda () (|f:ACL2::FN-IBP-TABLE-SEAL| {id} 3 page)) (lambda (status page) (unless (eq? status '|KEYWORD::SEALED|) (error \"seal\"))))", f"(|f:ACL2::FN-IBP-NODE-CHILDREN-PUT| '|ACL2::FN-IBP-TABLE-PAGE| page {parent})"])
    def observe(label, fuel=8, slot=0, depth=2, id=17, inc=3):
        query="(fn-miq-make 1 1 nil 1 1 1 nil 7 '(0 1 0) nil nil :probing)"
        sq="(|f:ACL2::FN-MIQ-MAKE| 1 1 '() 1 1 1 '() 7 '(0 1 0) '() '() '|KEYWORD::PROBING|)"
        c.append(f'(multiple-value-bind (status query candidate fuel) (fn-ibp-node-query-next {query} {fuel} {slot} {depth} {id} {inc} node) (assert (equal (list status query candidate fuel (fn-ibp-node-children-count node)) {cl.quoted(observations[label])})) (format t "PASS {label}~%"))')
        s.append(f'(call-with-values (lambda () (|f:ACL2::FN-IBP-NODE-QUERY-NEXT| {sq} {fuel} {slot} {depth} {id} {inc} node)) (lambda (status query candidate fuel) (unless (equal? (list status query candidate fuel (|f:ACL2::FN-IBP-NODE-CHILDREN-COUNT| node)) \'{chicken.scm_datum(observations[label])}) (error "mismatch {label}")) (print "PASS {label}")))')
    observe('EMPTY'); observe('YIELD',fuel=2)
    install(['fn-ibp-node-left','fn-ibp-node-left'],17,7,42)
    observe('LEFT'); observe('LEFT-REPEAT'); observe('STALE-INC',inc=4); observe('ABSENT-RIGHT',slot=1)
    install(['fn-ibp-node-right','fn-ibp-node-left'],19,7,11)
    observe('RIGHT',slot=1,id=19); observe('LEFT-PRESERVED')
    for label, tag, enc in [('TAG-MISS',8,42),('CORRUPT-ENCZERO',7,0)]:
        c.append('(fn-ibp-node-children-clear node)'); s.append('(|f:ACL2::FN-IBP-NODE-CHILDREN-CLEAR| node)')
        install([],17,tag,enc); observe(label,depth=0)
    Path(str(output)+'.lisp').write_text('\n'.join(c)+'\n')
    Path(str(output)+'.scm').write_text('\n'.join(s)+'\n')

if __name__ == '__main__':
    generate(*sys.argv[1:])
