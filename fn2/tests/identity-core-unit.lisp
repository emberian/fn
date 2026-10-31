; Layer C in the served core: the identity decision (C-S1) through the core
; wrappers fn2-identity-offer and fn2-identity-step, and a transaction's
; writes through the private successor (C-S3: fn2-successor-put / -arg /
; -arg-octets / -resolve / -stage / -out / -bind / -release / -publish /
; -drop), on the real assembled core under the tiny profile (two
; transactions, so two decision rows). The offer's octets sit in workspaces of an upload-shaped
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
      ((mv rel fn2-core) (fn2-successor-release 1 fn2-core))
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

;; C-S3, the identity case (C-S2's scenario through the seam that replaced
; it). A profile with 4 KiB pool slots for the engine's arenas and scratch.
; Offers m (content 7) and decide: :stored; a record slot, staged, bound into
; batch 1. A second decision for m (content 7), decided while batch 1 is
; private, answers :stored (the successor is invisible) and its stage refuses
; :stale once batch 1 is published (its bucket moved); releasing the bound
; transaction is refused :state. Decided again after publication: :duplicate.
; Content 8 for m: :conflict, bound into batch 2 as evidence, published;
; re-offered: :evidence. Message-ID n bound into batch 3, which is dropped: n
; is :stored again.
(defconst *fn2-icu-profile*
 (put-assoc-equal :identity-arena-bytes 4096
  (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096)) *fn2-profile-tiny*)))
(defun fn2-icu-decide (d mslot mgen mlen dslot dgen fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv code fn2-core) (fn2-identity-offer d mslot mgen 0 mlen dslot dgen 0 5 1 1 fn2-core))
      ((unless (eq code :ok)) (mv (list :offer code) fn2-core))
      ((mv answer & fn2-core) (fn2-icu-drive 100 d fn2-core)))
  (mv answer fn2-core)))
(defun fn2-icu-resolve (fuel tx fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel fn2-core)
  (mv-let (answer fn2-core) (fn2-successor-resolve tx 4096 fn2-core)
   (if (eq answer :more) (fn2-icu-resolve (- fuel 1) tx fn2-core) (mv answer fn2-core)))))
;; Slot 0 of TX records its decision's fact (article ARTICLE, principal 3); resolved.
(defun fn2-icu-record (tx article fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c1 fn2-core) (fn2-successor-put tx 0 1 :record fn2-core))
      ((mv c2 fn2-core) (fn2-successor-arg tx 0 0 :value article fn2-core))
      ((mv c3 fn2-core) (fn2-successor-arg tx 0 1 :value 3 fn2-core))
      ((mv c4 fn2-core) (fn2-icu-resolve 40 tx fn2-core)))
  (mv (if (and (eq c1 :ok) (eq c2 :ok) (eq c3 :ok) (eq c4 :ok)) :ok (list c1 c2 c3 c4)) fn2-core)))
(defun fn2-icu-stage (tx fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (mv-let (code i fn2-core) (fn2-successor-stage tx fn2-core) (mv (if (eq code :ok) :ok (list code i)) fn2-core)))
(defun fn2-icu-successor (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-icu-profile* fn2-core))
      ((mv & mslot mgen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & nslot ngen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & d7 g7 fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & d8 g8 fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & fn2-core) (fn2-icu-write *fn2-icu-mid* mslot mgen 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-write (append (butlast *fn2-icu-mid* 3) (list 64 121 62)) nslot ngen 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-write (make-list 32 :initial-element 7) d7 g7 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-write (make-list 32 :initial-element 8) d8 g8 0 fn2-core))
      (len (len *fn2-icu-mid*))
      ((mv a1 fn2-core) (fn2-icu-decide 0 mslot mgen len d7 g7 fn2-core))
      ((mv & fn2-core) (fn2-icu-record 0 100 fn2-core))
      ((mv s1 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv b1 fn2-core) (fn2-successor-bind 0 1 1 fn2-core))
      ((mv a2 fn2-core) (fn2-icu-decide 1 mslot mgen len d7 g7 fn2-core))
      ((mv r0 fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv p1 fn2-core) (fn2-successor-publish 1 fn2-core))
      ((mv r0b fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-record 1 100 fn2-core))
      ((mv s2 fn2-core) (fn2-icu-stage 1 fn2-core))
      ((mv a3 fn2-core) (fn2-icu-decide 1 mslot mgen len d7 g7 fn2-core))
      ((mv s3 fn2-core) (fn2-icu-stage 1 fn2-core))
      ((mv & fn2-core) (fn2-successor-release 1 fn2-core))
      ((mv a4 fn2-core) (fn2-icu-decide 0 mslot mgen len d8 g8 fn2-core))
      ((mv & fn2-core) (fn2-icu-record 0 101 fn2-core))
      ((mv s4 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv b4 fn2-core) (fn2-successor-bind 0 2 2 fn2-core))
      ((mv p2 fn2-core) (fn2-successor-publish 2 fn2-core))
      ((mv & fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv a5 fn2-core) (fn2-icu-decide 0 mslot mgen len d8 g8 fn2-core))
      ((mv & fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv a6 fn2-core) (fn2-icu-decide 1 nslot ngen len d7 g7 fn2-core))
      ((mv & fn2-core) (fn2-icu-record 1 102 fn2-core))
      ((mv s6 fn2-core) (fn2-icu-stage 1 fn2-core))
      ((mv b6 fn2-core) (fn2-successor-bind 1 3 3 fn2-core))
      ((mv x3 fn2-core) (fn2-successor-drop 3 fn2-core))
      ((mv r1 fn2-core) (fn2-successor-release 1 fn2-core))
      ((mv a7 fn2-core) (fn2-icu-decide 1 nslot ngen len d7 g7 fn2-core)))
  (mv (list :first a1 s1 b1 :private a2 :release-bound r0 :publish p1 r0b :stale s2 :after a3 s3
            :conflict a4 s4 b4 p2 :evidence a5 :dropped a6 s6 b6 x3 r1 a7)
      fn2-core)))
(defun fn2-icu-successor-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-icu-successor fn2-core) r)))
(assert-event
 (equal (fn2-icu-successor-result)
        '(:first :stored :ok :ok :private :stored :release-bound :state :publish :ok :ok :stale (:stale 0)
          :after :duplicate (:duplicate 0) :conflict :conflict :ok :ok :ok :evidence :evidence
          :dropped :stored :ok :ok :ok :ok :stored)))

;; C-S3, folds and inserts. A POST's writes in one transaction: the identity
; fact (slot 0), the group's accept (slot 1: group 9, its number assigned
; high + 1 at stage), the overview row (slot 2: number = slot 1's high by
; :out, position = the commit position by :event, the line by reference).
; The seam's refusals at put and arg. The accept's number is 1; a second
; transaction's accept in the same unpublished batch chains on the first's
; private row (2). After publication a withdrawal of a number past high is
; :refused (slot 0); a withdrawal of 2 staged and bound into batch 5, which
; is dropped, leaves the group as published, so the next accept is 3 with
; count 3. The identity fact is published with batch 4: m is :duplicate.
(defconst *fn2-icu-high* *fn2-group-counts-entry-field-high*)
(defconst *fn2-icu-count* *fn2-group-counts-entry-field-count*)
(defun fn2-icu-accept (tx slot group fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c1 fn2-core) (fn2-successor-put tx slot 5 :accept fn2-core))
      ((mv c2 fn2-core) (fn2-successor-arg tx slot 0 :value group fn2-core)))
  (mv (if (and (eq c1 :ok) (eq c2 :ok)) :ok (list c1 c2)) fn2-core)))
(defun fn2-icu-withdraw (tx group number fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c1 fn2-core) (fn2-successor-put tx 0 5 :withdraw fn2-core))
      ((mv c2 fn2-core) (fn2-successor-arg tx 0 0 :value group fn2-core))
      ((mv c3 fn2-core) (fn2-successor-arg tx 0 1 :value number fn2-core))
      ((mv c4 fn2-core) (fn2-icu-resolve 40 tx fn2-core)))
  (mv (if (and (eq c1 :ok) (eq c2 :ok) (eq c3 :ok) (eq c4 :ok)) :ok (list c1 c2 c3 c4)) fn2-core)))
(defun fn2-icu-folds (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-icu-profile* fn2-core))
      ((mv & mslot mgen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & d7 g7 fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & lslot lgen fn2-core) (fn2-core-reserve 0 5 1 1 fn2-core))
      ((mv & fn2-core) (fn2-icu-write *fn2-icu-mid* mslot mgen 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-write (make-list 32 :initial-element 7) d7 g7 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-write (make-list 20 :initial-element 83) lslot lgen 0 fn2-core))
      (len (len *fn2-icu-mid*))
      ((mv a1 fn2-core) (fn2-icu-decide 0 mslot mgen len d7 g7 fn2-core))
      ((mv & fn2-core) (fn2-successor-put 0 0 1 :record fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 0 0 :value 200 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 0 1 :value 3 fn2-core))
      ((mv & fn2-core) (fn2-icu-accept 0 1 9 fn2-core))
      ((mv & fn2-core) (fn2-successor-put 0 2 3 :insert fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 0 :value 9 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 1 :out (+ 256 *fn2-icu-high*) fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 2 :value 200 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 3 :event 0 fn2-core))
      ((mv o1 fn2-core) (fn2-successor-arg-octets 0 2 4 lslot lgen 0 20 5 1 1 fn2-core))
      ((mv v1 fn2-core) (fn2-successor-put 0 3 5 :insert fn2-core))
      ((mv v2 fn2-core) (fn2-successor-put 0 3 3 :record fn2-core))
      ((mv v3 fn2-core) (fn2-successor-put 0 3 3 :bogus fn2-core))
      ((mv v4 fn2-core) (fn2-successor-put 0 3 99 :insert fn2-core))
      ((mv v5 fn2-core) (fn2-successor-arg 0 1 1 :value 5 fn2-core))
      ((mv v6 fn2-core) (fn2-successor-arg 0 2 1 :out 512 fn2-core))
      ((mv v7 fn2-core) (fn2-successor-arg 0 2 4 :value 0 fn2-core))
      ((mv u1 & fn2-core) (fn2-successor-stage 0 fn2-core))
      ((mv r1 fn2-core) (fn2-icu-resolve 40 0 fn2-core))
      ((mv s1 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv h1 n1) (fn2-successor-out 0 1 *fn2-icu-high* fn2-core))
      ((mv & n2) (fn2-successor-out 0 2 *fn2-overview-entry-field-number* fn2-core))
      ((mv b1 fn2-core) (fn2-successor-bind 0 4 10 fn2-core))
      ((mv & n3) (fn2-successor-out 0 2 *fn2-overview-entry-field-position* fn2-core))
      ((mv & fn2-core) (fn2-icu-accept 1 0 9 fn2-core))
      ((mv & fn2-core) (fn2-icu-resolve 40 1 fn2-core))
      ((mv s2 fn2-core) (fn2-icu-stage 1 fn2-core))
      ((mv & n4) (fn2-successor-out 1 0 *fn2-icu-high* fn2-core))
      ((mv b2 fn2-core) (fn2-successor-bind 1 4 11 fn2-core))
      ((mv p4 fn2-core) (fn2-successor-publish 4 fn2-core))
      ((mv x0 fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv x1 fn2-core) (fn2-successor-release 1 fn2-core))
      ((mv & fn2-core) (fn2-icu-withdraw 0 9 99 fn2-core))
      ((mv w1 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-withdraw 0 9 2 fn2-core))
      ((mv w2 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv & n5) (fn2-successor-out 0 0 *fn2-icu-count* fn2-core))
      ((mv b5 fn2-core) (fn2-successor-bind 0 5 12 fn2-core))
      ((mv d5 fn2-core) (fn2-successor-drop 5 fn2-core))
      ((mv x2 fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-accept 0 0 9 fn2-core))
      ((mv & fn2-core) (fn2-icu-resolve 40 0 fn2-core))
      ((mv s3 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv & n6) (fn2-successor-out 0 0 *fn2-icu-high* fn2-core))
      ((mv & n7) (fn2-successor-out 0 0 *fn2-icu-count* fn2-core))
      ((mv & fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv a2 fn2-core) (fn2-icu-decide 1 mslot mgen len d7 g7 fn2-core)))
  (mv (list :decide a1 :octets o1 :refusals (list v1 v2 v3 v4 v5 v6 v7) :unresolved u1
            :post r1 s1 h1 n1 n2 b1 n3 :chained s2 n4 b2 p4 x0 x1
            :withdraw w1 w2 n5 b5 d5 x2 :next s3 n6 n7 :identity a2)
      fn2-core)))
(defun fn2-icu-folds-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-icu-folds fn2-core) r)))
(assert-event
 (equal (fn2-icu-folds-result)
        '(:decide :stored :octets :ok :refusals (:kind :kind :kind :schema :kind :kind :kind) :unresolved :state
          :post :ok :ok :ok 1 1 :ok 10 :chained :ok 2 :ok :ok :ok :ok
          :withdraw (:refused 0) :ok 1 :ok :ok :ok :next :ok 3 3 :identity :duplicate)))

; C-S3a, a late octet arg: an overview row whose line is declared at
; :prepare with its bound (20) and given only after stage. Declaring a late
; key field or integer field is :kind, a bound past the field's 1,024 is
; :bounds; a fill before stage is :state, of a field not declared late
; :kind, longer than the bound :bounds; bind before the fill is :state;
; the fill is :ok and a second one under another owner :owner. A stage
; again needs the fill again (bind :state, fill :ok). Bound and published,
; the overview overlay's arena holds the 20 line octets (S) and none of the
; 20 octets past them in the source (T).
(defun fn2-icu-overlay-of (k o sid fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix k)))
 (if (zp k) (mv 0 0 0)
  (mv-let (hit slot gen fl)
   (stobj-let ((fn2-overlays (fn2-core-overlays fn2-core)))
    (hit slot gen fl)
    (if (< o (fn2-overlays-rows fn2-overlays))
        (mv (and (equal (fn2-overlays-schema o fn2-overlays) sid)
                 (equal (fn2-overlays-phase o fn2-overlays) *fn2-overlay-phase-frozen*))
            (fn2-overlays-slot o fn2-overlays) (fn2-overlays-gen o fn2-overlays) (fn2-overlays-fill o fn2-overlays))
      (mv nil 0 0 0))
    (mv hit slot gen fl))
   (if hit (mv slot gen fl) (fn2-icu-overlay-of (- k 1) (+ 1 o) sid fn2-core)))))
(defun fn2-icu-count-byte (n byte slot gen idx fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil :measure (nfix n)))
 (if (zp n) 0
  (mv-let (code b) (fn2-core-read slot gen idx *fn2-idc-owner-kind* *fn2-idc-owner-slot* *fn2-idc-owner-gen* fn2-core)
   (+ (if (and (eq code :ok) (equal b byte)) 1 0) (fn2-icu-count-byte (- n 1) byte slot gen (+ 1 idx) fn2-core)))))
(defun fn2-icu-late (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-icu-profile* fn2-core))
      ((mv & lslot lgen fn2-core) (fn2-core-reserve 0 5 1 1 fn2-core))
      ((mv & fn2-core) (fn2-icu-write (append (make-list 20 :initial-element 83) (make-list 20 :initial-element 84))
                                      lslot lgen 0 fn2-core))
      ((mv & fn2-core) (fn2-icu-accept 0 0 9 fn2-core))
      ((mv & fn2-core) (fn2-successor-put 0 1 3 :insert fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 1 0 :value 9 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 1 1 :out *fn2-icu-high* fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 1 2 :value 200 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 1 3 :event 0 fn2-core))
      ((mv k1 fn2-core) (fn2-successor-arg-octets-late 0 1 0 20 fn2-core))
      ((mv k2 fn2-core) (fn2-successor-arg-octets-late 0 1 2 20 fn2-core))
      ((mv k3 fn2-core) (fn2-successor-arg-octets-late 0 1 4 2000 fn2-core))
      ((mv l1 fn2-core) (fn2-successor-arg-octets-late 0 1 4 20 fn2-core))
      ((mv f0 fn2-core) (fn2-successor-fill-octets 0 1 4 lslot lgen 0 20 5 1 1 fn2-core))
      ((mv r1 fn2-core) (fn2-icu-resolve 40 0 fn2-core))
      ((mv s1 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv f1 fn2-core) (fn2-successor-fill-octets 0 1 3 lslot lgen 0 20 5 1 1 fn2-core))
      ((mv f2 fn2-core) (fn2-successor-fill-octets 0 1 4 lslot lgen 0 21 5 1 1 fn2-core))
      ((mv b0 fn2-core) (fn2-successor-bind 0 4 10 fn2-core))
      ((mv f3 fn2-core) (fn2-successor-fill-octets 0 1 4 lslot lgen 0 20 5 1 1 fn2-core))
      ((mv f4 fn2-core) (fn2-successor-fill-octets 0 1 4 lslot lgen 0 20 5 1 2 fn2-core))
      ((mv s2 fn2-core) (fn2-icu-stage 0 fn2-core))
      ((mv b1 fn2-core) (fn2-successor-bind 0 4 10 fn2-core))
      ((mv f5 fn2-core) (fn2-successor-fill-octets 0 1 4 lslot lgen 0 20 5 1 1 fn2-core))
      ((mv b2 fn2-core) (fn2-successor-bind 0 4 10 fn2-core))
      ((mv p4 fn2-core) (fn2-successor-publish 4 fn2-core))
      ((mv aslot agen fl) (fn2-icu-overlay-of 64 0 3 fn2-core)))
  (mv (list :declare k1 k2 k3 l1 :early f0 :staged r1 s1 :fill f1 f2 b0 f3 f4 :again s2 b1 f5 b2 p4
            :arena (fn2-icu-count-byte fl 83 aslot agen 0 fn2-core) (fn2-icu-count-byte fl 84 aslot agen 0 fn2-core))
      fn2-core)))
(defun fn2-icu-late-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-icu-late fn2-core) r)))
(assert-event
 (equal (fn2-icu-late-result)
        '(:declare :kind :kind :bounds :ok :early :state :staged :ok :ok :fill :kind :bounds :state :ok :owner
          :again :ok :state :ok :ok :ok :arena 20 0)))
