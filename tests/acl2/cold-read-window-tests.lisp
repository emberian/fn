(in-package "ACL2")
(include-book "../../books/cold-read-window")
(include-book "std/testing/assert-bang" :dir :system)
(defconst *crw-small* '(1 0 4096 64 1024 0 0))
(defconst *crw-large* '(1 0 1099511627776 64 1024 0 0))
(assert! (and (fn-crw-supportedp *crw-small* 1)
              (fn-crw-job-demand *crw-small* 1)
              (equal (cdr (fn-crw-job-demand *crw-small* 1)) '(0 0 1 1))))
; A terabyte protected frame still uses the same fixed buffers/inventory.
(assert! (equal (fn-crw-job-demand *crw-small* 1)
                (fn-crw-job-demand *crw-large* 1)))
(assert! (< (car (fn-crw-job-demand *crw-small* 1)) 262144))
; Process-local identities are naturals, not quietly truncated u64s.
(assert! (< (car (fn-crw-job-demand *crw-small* 1))
             (car (fn-crw-job-demand *crw-small* (expt 2 4096)))))
; Successor identity crosses a selected-layout limb/alignment boundary.
; Mutation witness: charging only the old ticket's normalized object would
; undercharge NEXT+1. The actual ceiling includes the spent successor.
(assert!
 (let ((ticket (- (expt 2 319) 1)))
   (and (fn-crw-supportedp *crw-small* ticket)
        (equal (fn-crl-natural-octets ticket) 48)
        (equal (fn-crl-natural-octets (+ 1 ticket)) 64)
        (< (fn-crl-natural-octets ticket) (fn-crl-natural-octets (+ 1 ticket)))
        (<= (fn-crl-natural-octets (+ 1 ticket))
            (fn-crl-natural-octets (fn-crw-natural-ceiling *crw-small* ticket))))))
(assert! (not (fn-crw-job-demand '(1 0 100 90 20 0 0) 1)))
(assert! (not (fn-crw-job-demand '(1 0 100 0 100 101 0) 1)))
(assert! (not (fn-crw-job-demand '(1 0 100 0 100 0 0 . bad) 1)))
(assert! (not (fn-crw-job-demand '(1 0 100 0 100 0 0) -1)))
(assert! (not (fn-crw-job-demand (list 1 0 100 0 100 0 (expt 2 257)) 1)))
(assert! (fn-crw-job-demand (list 1 0 (- (expt 2 63) 33) 0 64 0 0) 1))
(assert! (not (fn-crw-job-demand (list 1 0 (- (expt 2 63) 32) 0 64 0 0) 1)))
; Backing has the three byte arrays and real general-register storage.
(assert! (> (fn-crw-decoder-backing-octets 1024 2048) (+ 65536 3494 64)))
(assert! (< (fn-crw-decoder-backing-octets 1024 2048)
             (fn-crw-decoder-backing-octets (expt 2 80) (expt 2 80))))
