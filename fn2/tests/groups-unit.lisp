; Layer C in the served core, the seams of D5's :prepare: the group directory
; (S-GROUP: genesis from the profile's :groups, fn2-group-lookup), the
; operation outcome schema (S-OUTCOME) through the private successor, and the
; article identifier as the commit position (S-ARTICLE-ID: :event on the
; article row's key and on the identity record's article). The real
; assembled core under the tiny profile with 4 KiB engine arenas.
; Run: sh fn2/tools/certify.sh tests/groups-unit.lisp
(in-package "ACL2")
(include-book "../books/assembly")
(include-book "std/util/bstar" :dir :system)

(defconst *fn2-gu-profile*
 (put-assoc-equal :groups '(("comp.lang.lisp" . 7) ("alt.test" . 9) ("misc.misc" . 11))
  (put-assoc-equal :identity-arena-bytes 4096
   (put-assoc-equal :pool-classes '((8 . 64) (4 . 256) (16 . 4096)) *fn2-profile-tiny*))))
(defun fn2-gu-write (bytes slot gen off fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (atom bytes) (mv :ok fn2-core)
  (mv-let (code fn2-core) (fn2-core-write slot gen off (car bytes) 5 1 1 fn2-core)
   (if (eq code :ok) (fn2-gu-write (cdr bytes) slot gen (+ 1 off) fn2-core) (mv code fn2-core)))))
(defun fn2-gu-chars (cs) (declare (xargs :verify-guards nil)) (if (atom cs) nil (cons (char-code (car cs)) (fn2-gu-chars (cdr cs)))))
; Look NAME up for TX to the end; (answer group calls).
(defun fn2-gu-drive (fuel tx slot gen len budget fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel 0 0 fn2-core)
  (mv-let (code group fn2-core) (fn2-group-lookup tx slot gen 0 len 5 1 1 budget fn2-core)
   (if (eq code :more)
       (mv-let (c g n fn2-core) (fn2-gu-drive (- fuel 1) tx slot gen len budget fn2-core) (mv c g (+ 1 n) fn2-core))
     (mv code group 1 fn2-core)))))
(defun fn2-gu-lookup (name tx fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv & slot gen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      (octets (fn2-gu-chars (coerce name 'list)))
      ((mv & fn2-core) (fn2-gu-write octets slot gen 0 fn2-core))
      ((mv code group calls fn2-core) (fn2-gu-drive 20 tx slot gen (len octets) 4096 fn2-core))
      ((mv & fn2-core) (fn2-core-release slot gen 5 1 1 fn2-core)))
  (mv (list code group calls) fn2-core)))

;; Genesis and lookups. Each configured name answers its group after two
;; calls (the start, then the genesis overlay); a name no group has, a prefix
;; of one and one a byte longer answer :absent after the run leg (three
;; calls: no run is installed). A name of 251 octets is :bounds; a lookup
;; while the transaction's identity decision is in flight is :state. A
;; profile naming one group twice is refused :duplicate at genesis; a group
;; of identifier 0 is :groups.
(defun fn2-gu-run (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-gu-profile* fn2-core))
      ((mv g fn2-core) (fn2-groups-genesis *fn2-gu-profile* fn2-core))
      ((mv l1 fn2-core) (fn2-gu-lookup "comp.lang.lisp" 0 fn2-core))
      ((mv l2 fn2-core) (fn2-gu-lookup "alt.test" 1 fn2-core))
      ((mv l3 fn2-core) (fn2-gu-lookup "misc.misc" 0 fn2-core))
      ((mv l4 fn2-core) (fn2-gu-lookup "alt.tests" 0 fn2-core))
      ((mv l5 fn2-core) (fn2-gu-lookup "alt.tes" 0 fn2-core))
      ((mv l6 fn2-core) (fn2-gu-lookup "rec.arts" 0 fn2-core))
      ((mv & slot gen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv long & fn2-core) (fn2-group-lookup 0 slot gen 0 251 5 1 1 4096 fn2-core))
      ((mv & fn2-core) (fn2-gu-write (make-list 32 :initial-element 7) slot gen 0 fn2-core))
      ((mv & fn2-core) (fn2-identity-offer 1 slot gen 0 20 slot gen 0 5 1 1 fn2-core))
      ((mv busy & fn2-core) (fn2-group-lookup 1 slot gen 0 8 5 1 1 4096 fn2-core))
      (twice (put-assoc-equal :groups '(("a.b" . 1) ("a.b" . 2)) *fn2-gu-profile*))
      (fn2-core (fn2-core-init twice fn2-core))
      ((mv dup fn2-core) (fn2-groups-genesis twice fn2-core))
      (zero (put-assoc-equal :groups '(("a.b" . 0)) *fn2-gu-profile*))
      (fn2-core (fn2-core-init zero fn2-core))
      ((mv bad fn2-core) (fn2-groups-genesis zero fn2-core))
      (fn2-core (fn2-core-init *fn2-profile-tiny* fn2-core))
      ((mv none fn2-core) (fn2-groups-genesis *fn2-profile-tiny* fn2-core))
      ((mv l7 fn2-core) (fn2-gu-lookup "alt.test" 0 fn2-core)))
  (mv (list :genesis g :found l1 l2 l3 :absent l4 l5 l6 :long long :busy busy :dup dup :bad bad :none none l7) fn2-core)))
(defun fn2-gu-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-gu-run fn2-core) r)))
(assert-event
 (equal (fn2-gu-result)
        '(:genesis :ok :found (:ok 7 2) (:ok 9 2) (:ok 11 2) :absent (:absent 0 4) (:absent 0 4) (:absent 0 4)
          :long :bounds :busy :state :dup :duplicate :bad :groups :none :ok (:absent 0 3))))

;; S-OUTCOME and S-ARTICLE-ID. Transaction 0 writes, in one batch: the
; outcome of (principal 3, operation 5) (request digest by reference, reply
; 240, the event), and the article row keyed by the commit position (:event
; on its key). Its identity record takes the article as :event too; the
; principal never (:kind). After publication the bound identity fact's
; article is the event, 42, and a second transaction's outcome for (3, 5)
; is :duplicate at stage.
(defconst *fn2-gu-mid* (append (list 60) (make-list 12 :initial-element 98) (list 64 120 62)))
(defun fn2-gu-resolve (fuel tx fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel fn2-core)
  (mv-let (answer fn2-core) (fn2-successor-resolve tx 4096 fn2-core)
   (if (eq answer :more) (fn2-gu-resolve (- fuel 1) tx fn2-core) (mv answer fn2-core)))))
(defun fn2-gu-decide (fuel d fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (if (zp fuel) (mv :fuel fn2-core)
  (mv-let (answer fn2-core) (fn2-identity-step d 4096 fn2-core)
   (if (eq answer :more) (fn2-gu-decide (- fuel 1) d fn2-core) (mv answer fn2-core)))))
(defun fn2-gu-outcome (tx i dslot dgen fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* (((mv c1 fn2-core) (fn2-successor-put tx i 9 :insert fn2-core))
      ((mv c2 fn2-core) (fn2-successor-arg tx i 0 :value 3 fn2-core))
      ((mv c3 fn2-core) (fn2-successor-arg tx i 1 :value 5 fn2-core))
      ((mv c4 fn2-core) (fn2-successor-arg-octets tx i 2 dslot dgen 0 32 5 1 1 fn2-core))
      ((mv c5 fn2-core) (fn2-successor-arg tx i 3 :value 240 fn2-core))
      ((mv c6 fn2-core) (fn2-successor-arg tx i 4 :event 0 fn2-core)))
  (mv (list c1 c2 c3 c4 c5 c6) fn2-core)))
; The article field of the identity fact in the newest published identity
; overlay (its entry 0), decoded into transaction 1's stripe.
(defun fn2-gu-bound-article (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (stobj-let ((fn2-overlays (fn2-core-overlays fn2-core)) (fn2-overlay-index (fn2-core-overlay-index fn2-core))
             (fn2-fields (fn2-core-fields fn2-core)) (fn2-pool (fn2-core-pool fn2-core)))
  (code article fn2-fields)
  (b* ((rows (fn2-overlays-rows fn2-overlays))
       (o (fn2-xl-newest-frozen rows 0 1 *fn2-u60-max* rows fn2-overlays))
       (eb (- (fn2-fields-rows fn2-fields) 200))
       ((mv code & fn2-fields) (fn2-ov-entry o 0 eb fn2-overlays fn2-overlay-index fn2-fields fn2-pool)))
   (mv code (fn2-fields-value (+ eb *fn2-identity-entry-field-article*) fn2-fields) fn2-fields))
  (mv code article fn2-core)))
(defun fn2-gu-ids (fn2-core)
 (declare (xargs :stobjs fn2-core :verify-guards nil))
 (b* ((fn2-core (fn2-core-init *fn2-gu-profile* fn2-core))
      ((mv & mslot mgen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & dslot dgen fn2-core) (fn2-core-reserve 1 5 1 1 fn2-core))
      ((mv & fn2-core) (fn2-gu-write *fn2-gu-mid* mslot mgen 0 fn2-core))
      ((mv & fn2-core) (fn2-gu-write (make-list 32 :initial-element 7) dslot dgen 0 fn2-core))
      ((mv & fn2-core) (fn2-identity-offer 0 mslot mgen 0 (len *fn2-gu-mid*) dslot dgen 0 5 1 1 fn2-core))
      ((mv a1 fn2-core) (fn2-gu-decide 100 0 fn2-core))
      ((mv & fn2-core) (fn2-successor-put 0 0 1 :record fn2-core))
      ((mv e1 fn2-core) (fn2-successor-arg 0 0 0 :event 0 fn2-core))
      ((mv e2 fn2-core) (fn2-successor-arg 0 0 1 :event 0 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 0 1 :value 3 fn2-core))
      ((mv o1 fn2-core) (fn2-gu-outcome 0 1 dslot dgen fn2-core))
      ((mv & fn2-core) (fn2-successor-put 0 2 2 :insert fn2-core))
      ((mv e3 fn2-core) (fn2-successor-arg 0 2 0 :event 0 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 1 :event 0 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 2 :value 0 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 3 :value 1 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg-octets 0 2 4 dslot dgen 0 32 5 1 1 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 5 :value 100 fn2-core))
      ((mv & fn2-core) (fn2-successor-arg 0 2 6 :value 3 fn2-core))
      ((mv r1 fn2-core) (fn2-gu-resolve 40 0 fn2-core))
      ((mv s1 & fn2-core) (fn2-successor-stage 0 fn2-core))
      ((mv b1 fn2-core) (fn2-successor-bind 0 1 42 fn2-core))
      ((mv p1 fn2-core) (fn2-successor-publish 1 fn2-core))
      ((mv x1 fn2-core) (fn2-successor-release 0 fn2-core))
      ((mv c art fn2-core) (fn2-gu-bound-article fn2-core))
      ((mv o2 fn2-core) (fn2-gu-outcome 1 0 dslot dgen fn2-core))
      ((mv r2 fn2-core) (fn2-gu-resolve 40 1 fn2-core))
      ((mv s2 i2 fn2-core) (fn2-successor-stage 1 fn2-core)))
  (mv (list :decide a1 :record-event e1 e2 :outcome o1 :article-key e3 :post r1 s1 b1 p1 x1 :article c art
            :again o2 r2 s2 i2)
      fn2-core)))
(defun fn2-gu-ids-result ()
 (declare (xargs :verify-guards nil))
 (with-local-stobj fn2-core (mv-let (r fn2-core) (fn2-gu-ids fn2-core) r)))
(assert-event
 (equal (fn2-gu-ids-result)
        '(:decide :stored :record-event :ok :kind :outcome (:ok :ok :ok :ok :ok :ok) :article-key :ok
          :post :ok :ok :ok :ok :ok :article :ok 42
          :again (:ok :ok :ok :ok :ok :ok) :ok :duplicate 0)))
