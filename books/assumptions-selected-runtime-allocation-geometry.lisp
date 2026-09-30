; A-SELECTED-RUNTIME-ALLOCATION-GEOMETRY. Conditional ordinary allocator unit.
; This is a qualification target, not a C/SBCL proof or installed allowance.
(in-package "ACL2")
(defconst *fn-srag-coordinate*
 '(:sbcl "2.6.8" :x86-64-linux :word-octets 8
   :toolchain "fcedce7e3aa26e7ef93c7b3801bc39b2c56b7968cc1dfdf8e710a8931b349d52"
   :gencgc-source "82d7e992cc2eb682829bae6ef25d9622d3fa3a9e9e1ac2c0dcb83d4a4fef1770"
   :page-octets 32768 :granularity-octets 0
   :ordinary-regions :arena-absent :allocation-profiler-off
   :restart-within-prefix :tail-pages-free :allocator-lock-held))
(defun fn-srag-coordinate-p (coordinate)
 (declare (xargs :guard t)) (equal coordinate *fn-srag-coordinate*))
(defun fn-srag-request-domain-p (request page granularity coordinate)
 (declare (xargs :guard t))
 (and (fn-srag-coordinate-p coordinate) (posp request)
      (< request (expt 2 44)) (equal page 32768) (equal granularity 0)))
; x86-64 lisp_alloc may obtain an initial region AND proactively refill it.
; Each ordinary search needs at most its goal plus one page of rounding.
; The second request is at most six 8-byte words. This conservative charge
; exceeds their sum. It excludes collection/copy, hooks, arenas, profiling,
; first-use and external allocations. Prefix/hint conditions must be qualified.
(defun fn-srag-request-prefix-demand (request page granularity)
 (declare (xargs :guard t))
 (* 2 (+ (nfix request) (nfix granularity) (nfix page) 48)))
(encapsulate
 (((fn-assume-srag-request-prefix-growth * * * *) => *))
 (local
  (defun fn-assume-srag-request-prefix-growth (request page granularity coordinate)
   (declare (ignore request page granularity coordinate)) 0))
 (defthm fn-assume-srag-request-prefix-growth-natural
  (natp (fn-assume-srag-request-prefix-growth request page granularity coordinate))
  :rule-classes :type-prescription)
 (defthm fn-assume-srag-ordinary-request-prefix-bound
  (implies (fn-srag-request-domain-p request page granularity coordinate)
   (<= (fn-assume-srag-request-prefix-growth request page granularity coordinate)
       (fn-srag-request-prefix-demand request page granularity)))
  :rule-classes nil))
; Proof-only roster: the served evaluator uses internally source-derived
; scalar counts. No host-supplied list or this subtotal installs authority.
(defun fn-srag-roster-domain-p (requests page granularity coordinate)
 (declare (xargs :guard t))
 (if (consp requests)
  (and (fn-srag-request-domain-p (car requests) page granularity coordinate)
       (fn-srag-roster-domain-p (cdr requests) page granularity coordinate))
  (null requests)))
(defun fn-srag-roster-request-octets (requests)
 (declare (xargs :guard t))
 (if (consp requests) (+ (nfix (car requests))
                         (fn-srag-roster-request-octets (cdr requests))) 0))
(defun fn-srag-assumed-roster-growth (requests page granularity coordinate)
 (declare (xargs :guard t))
 (if (consp requests)
  (+ (fn-assume-srag-request-prefix-growth (car requests) page granularity coordinate)
     (fn-srag-assumed-roster-growth (cdr requests) page granularity coordinate)) 0))
(defun fn-srag-counted-prefix-demand (request-octets request-count page granularity)
 (declare (xargs :guard t))
 (+ (* 2 (nfix request-octets))
    (* (nfix request-count) (* 2 (+ (nfix page) (nfix granularity) 48)))))
(defthm fn-srag-counted-prefix-demand-natural
 (natp (fn-srag-counted-prefix-demand request-octets request-count page granularity))
 :rule-classes :type-prescription)
(defthm fn-srag-assumed-roster-within-counted-prefix-demand
 (implies (fn-srag-roster-domain-p requests page granularity coordinate)
  (<= (fn-srag-assumed-roster-growth requests page granularity coordinate)
      (fn-srag-counted-prefix-demand (fn-srag-roster-request-octets requests)
                                    (len requests) page granularity)))
 :hints (("Goal" :induct (fn-srag-assumed-roster-growth requests page granularity coordinate)
           :in-theory (enable fn-srag-request-prefix-demand))
         ("Subgoal *1/1" :use ((:instance fn-assume-srag-ordinary-request-prefix-bound
                                  (request (car requests))))))
 :rule-classes nil)
