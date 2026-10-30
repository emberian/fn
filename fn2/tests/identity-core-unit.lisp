; Layer C in the served core (C-S1): the identity decision through the core
; wrappers fn2-identity-offer, fn2-identity-step and fn2-identity-release on
; the real assembled core under the tiny profile (two transactions, so two
; decision rows). The offer's octets sit in workspaces of an upload-shaped
; owner (kind 5, slot 1, generation 1), as layer D's upload holds them.
; Run: sh fn2/tools/certify.sh tests/identity-core-unit.lisp
(in-package "ACL2")
(include-book "../books/assembly")
(include-book "std/util/bstar" :dir :system)

(defun fn2-icu-write (bytes slot gen off fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom bytes) (mv :ok fn2-core)
  (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 5 1 1 fn2-core)
   (if (eq code :ok) (fn2-icu-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-icu-drive (fuel d fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 fn2-core)
  (mv-let (answer fn2-core) (fn2-identity-step d 4096 fn2-core)
   (if (eq answer :more)
       (mv-let (a n fn2-core) (fn2-icu-drive (- fuel 1) d fn2-core) (mv a (+ 1 n) fn2-core))
     (mv answer 1 fn2-core)))))
(defconst *fn2-icu-mid* (append (list 60) (make-list 40 :initial-element 97) (list 64 120 62)))

; Decision 1 of a fresh node: the offer is :stored (no fact is visible), in
; three steps (no overlay, no run, the answer); a second offer to the busy row is
; refused :state, an offer to a row past the profile's two is :bounds, and
; a released row takes an offer again. A Message-ID longer than 250 octets
; is refused :bounds before anything is staged.
(defun fn2-icu-run (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
      ((mv c1 mslot mgen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv c2 dslot dgen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv c3 fn2-core) (fn2-icu-write *fn2-icu-mid* mslot mgen 0 fn2-core))
      ((mv c4 fn2-core) (fn2-icu-write (make-list 32 :initial-element 7) dslot dgen 0 fn2-core))
      ((mv offer fn2-core) (fn2-identity-offer 1 mslot mgen 0 (len *fn2-icu-mid*) dslot dgen 0 5 1 1 fn2-core))
      ((mv busy fn2-core) (fn2-identity-offer 1 mslot mgen 0 (len *fn2-icu-mid*) dslot dgen 0 5 1 1 fn2-core))
      ((mv past fn2-core) (fn2-identity-offer 2 mslot mgen 0 (len *fn2-icu-mid*) dslot dgen 0 5 1 1 fn2-core))
      ((mv long fn2-core) (fn2-identity-offer 0 mslot mgen 0 251 dslot dgen 0 5 1 1 fn2-core))
      ((mv answer steps fn2-core) (fn2-icu-drive 100 1 fn2-core))
      ((mv again fn2-core) (fn2-identity-step 1 4096 fn2-core))
      ((mv rel fn2-core) (fn2-identity-release 1 fn2-core))
      ((mv idle fn2-core) (fn2-identity-step 1 4096 fn2-core))
      ((mv reoffer fn2-core) (fn2-identity-offer 1 mslot mgen 0 (len *fn2-icu-mid*) dslot dgen 0 5 1 1 fn2-core))
      ((mv answer2 & fn2-core) (fn2-icu-drive 100 1 fn2-core)))
  (mv (list :setup (list c1 c2 c3 c4) :offer offer :busy busy :past past :long long
            :answer answer :steps steps :again again :release rel :idle idle :reoffer reoffer :answer2 answer2)
      fn2-core)))
(defun fn2-icu-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-icu-run fn2-core) r)))
(assert-event
 (equal (fn2-icu-result)
        '(:setup (:ok :ok :ok :ok) :offer :ok :busy :state :past :bounds :long :bounds
          :answer :stored :steps 3 :again :stored :release :ok :idle :state :reoffer :ok :answer2 :stored)))
