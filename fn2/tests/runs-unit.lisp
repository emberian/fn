; Layer C1 unit: one run page written, sealed by B's sealer, accepted by B's
; checker, refused after a flipped byte, and searched by the generated seek;
; multi-page runs, scans and the overlay. Over the production schemas
; (C-ONE-ASSEMBLY): overview (numeric key) and identity (octet key); the
; identity schema's keystone teeth are identity-unit's.
(in-package "ACL2")
(include-book "runs-assembly")
(include-book "std/util/bstar" :dir :system)



; Fixture owner (an MRef C's engine would hold) and field-row plan.
(defconst *fn2-rt-owner* '(9 0 1))
(defconst *fn2-rt-writer-base* 0)
(defconst *fn2-rt-entry-base* 200)
(defconst *fn2-rt-reader-base* 300)
(defconst *fn2-rt-query-base* 420)
(defconst *fn2-rt-hash-row* 136)

;; Nest WITH-LOCAL-STOBJ over STOBJS around BODY, which returns
;; (mv answer s1 ... sn); the nest returns ANSWER.
(defun fn2-rt-nest (k stobjs e)
 (declare (xargs :verify-guards nil))
 (if (zp k) e
  (let ((held (take k stobjs)))
   (fn2-rt-nest (- k 1) stobjs
    `(with-local-stobj ,(nth (- k 1) stobjs)
      (mv-let (answer ,@held) ,e
       ,(if (= k 1) 'answer `(mv answer ,@(take (- k 1) stobjs)))))))))
(defmacro fn2-rt-with (stobjs body)
 (fn2-rt-nest (len stobjs) stobjs body))
(defconst *fn2-rt-stobjs*
 '(fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))

(defmacro fn2-rt-defun (name args body)
 `(defun ,name ,(append args *fn2-rt-stobjs*)
   (declare (xargs :stobjs ,*fn2-rt-stobjs* :verify-guards nil))
   ,body))
(defmacro fn2-rt-mv (&rest values) `(mv ,@values ,@*fn2-rt-stobjs*))

(fn2-rt-defun fn2-rt-setup ()
 (b* ((fn2-run-writers (fn2-run-writers-init 1 fn2-run-writers))
      (fn2-run-restarts (fn2-run-restarts-init *fn2-run-restart-capacity* fn2-run-restarts))
      (fn2-fields (fn2-fields-init 512 fn2-fields))
      (fn2-pool (fn2-pool-init '((2 . 65536) (2 . 4096)) 1 100 fn2-pool))
      (fn2-fc (fn2-fc-init 1 fn2-fc))
      (fn2-fc-context (fn2-fc-context-init 1 fn2-fc-context))
      (fn2-b3 (fn2-b3-table-init 1 fn2-b3))
      (fn2-digests (fn2-digests-init 140 fn2-digests)))
  (fn2-rt-mv :ok)))

; Overview entry i: group 1, number 2(i+1), article 100+i, position 2(i+1),
; line "A" (one octet at offset 0 of the source workspace LSLOT/LGEN).
(fn2-rt-defun fn2-rt-num-add-loop (fuel i lslot lgen)
 (if (zp fuel) (fn2-rt-mv :ok i)
  (b* ((e *fn2-rt-entry-base*)
       (fn2-fields (fn2-fields-set-value (+ e *fn2-overview-entry-field-group*) 1 fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ e *fn2-overview-entry-field-number*) (* 2 (+ 1 i)) fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ e *fn2-overview-entry-field-article*) (+ 100 i) fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ e *fn2-overview-entry-field-position*) (* 2 (+ 1 i)) fn2-fields))
       (fn2-fields (fn2-fields-put (+ e *fn2-overview-entry-field-line*) (ref-slot lslot) (ref-gen lgen) (ref-off 0) (ref-len 1)))
       ((mv code fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
        (fn2-run-add 0 3 e fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
   (if (eq code :ok) (fn2-rt-num-add-loop (- fuel 1) (+ 1 i) lslot lgen
                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-rt-mv code i)))))

(fn2-rt-defun fn2-rt-close (fuel)
 (if (zp fuel) (fn2-rt-mv :fuel)
  (b* (((mv code fn2-run-writers fn2-fields fn2-pool)
        (fn2-run-close-step 0 4096 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
   (if (eq code :more)
       (fn2-rt-close (- fuel 1) fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-rt-mv code)))))

(fn2-rt-defun fn2-rt-seal (fuel)
 (if (zp fuel) (fn2-rt-mv :fuel)
  (b* (((mv code fn2-run-writers fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
        (fn2-run-seal-step 0 0 *fn2-rt-hash-row* 4096 fn2-run-writers fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
   (if (eq code :more)
       (fn2-rt-seal (- fuel 1) fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-rt-mv code)))))

; B's checker, not the sealer: the page against its parent-held hash.
(fn2-rt-defun fn2-rt-check (slot gen)
 (b* (((mv code fn2-fc fn2-b3 fn2-fields fn2-pool fn2-digests)
       (fn2-format-drive (fn2-format-fuel *fn2-run-page-size*) 0 :page nil slot gen 0 *fn2-run-page-size*
                         *fn2-rt-writer-base* 9 0 1 4096 fn2-fc fn2-fc-context fn2-b3 fn2-fields fn2-pool fn2-digests)))
  (fn2-rt-mv code)))

(fn2-rt-defun fn2-rt-num-seek (slot gen group number)
 (b* ((q *fn2-rt-query-base*) (rb *fn2-rt-reader-base*)
      (fn2-fields (fn2-fields-set-value (+ q *fn2-overview-entry-field-group*) group fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ q *fn2-overview-entry-field-number*) number fn2-fields))
      ((mv code fn2-fields) (fn2-run-read-header slot gen rb 9 0 1 fn2-fields fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :header code)))
      ((mv code & & idx & fn2-fields)
       (fn2-run-seek 3 0 64 0 (fn2-run-hdr rb restarts) 0 0 q rb slot gen 9 0 1 9 0 1 fn2-fields fn2-pool))
      (article (if (eq code :found) (fn2-fields-value (+ rb *fn2-run-reader-entry* *fn2-overview-entry-field-article*) fn2-fields) nil)))
  (fn2-rt-mv (list code idx article))))

(fn2-rt-defun fn2-rt-seeks (slot gen queries)
 (if (atom queries) (fn2-rt-mv nil)
  (b* (((mv one fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rt-num-seek slot gen (caar queries) (cadar queries)
                         fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
       ((mv rest fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rt-seeks slot gen (cdr queries)
                      fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (fn2-rt-mv (cons one rest)))))

; The page scenario: N entries (0 means fill until :full), close, head, seal,
; check, then the queries, then one flipped payload byte and a recheck.
(fn2-rt-defun fn2-rt-num-page (n queries)
 (b* (((mv & fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-setup fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv code slot gen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :reserve code)))
      ((mv & lslot lgen fn2-pool) (fn2-pool-reserve 1 9 0 1 fn2-pool))
      ((mv & fn2-pool) (fn2-pool-write lslot lgen 0 65 9 0 1 fn2-pool))
      ((mv code fn2-run-writers fn2-pool)
       (fn2-run-open 0 slot gen 3 1 0 7 0 *page-kind-run-data* 5 2 3 1 1 9 0 1 *fn2-rt-writer-base* *fn2-run-page-size* fn2-run-writers fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :open code)))
      ((mv add count fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-num-add-loop (if (zp n) 100000 n) 0 lslot lgen fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv & fn2-run-writers) (fn2-run-close 0 fn2-run-writers))
      ((mv close fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-close 64 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv head fn2-run-writers fn2-fields fn2-pool) (fn2-run-head 0 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      (fn2-fc-context (fn2-run-seal-context 0 0 *fn2-rt-hash-row* fn2-run-writers fn2-fc-context))
      ((mv seal fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-seal 64 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv check fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-check slot gen fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv seeks fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-seeks slot gen queries fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv byte-code byte) (fn2-pool-read slot gen 1000 9 0 1 fn2-pool))
      ((mv & fn2-pool) (fn2-pool-write slot gen 1000 (logxor 1 (nfix byte)) 9 0 1 fn2-pool))
      ((mv flipped fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-check slot gen fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
  (fn2-rt-mv (list :add add count :close close :head head :seal seal :check check
                   :restarts (fn2-run-writers-restarts 0 fn2-run-writers)
                   :cursor (fn2-run-writers-cursor 0 fn2-run-writers)
                   :seeks seeks :flip byte-code flipped))))
(defun fn2-rt-num-page-result (n queries)
 (declare (xargs :verify-guards nil))
 (fn2-rt-with (fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
  (fn2-rt-num-page n queries fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))


(defun fn2-rt-write-bytes (bytes slot gen off okind oslot ogen fn2-pool)
 (declare (xargs :stobjs fn2-pool :verify-guards nil))
 (if (atom bytes) (mv :ok fn2-pool)
  (mv-let (code fn2-pool) (fn2-pool-write slot gen off (car bytes) okind oslot ogen fn2-pool)
   (if (eq code :ok) (fn2-rt-write-bytes (cdr bytes) slot gen (+ 1 off) okind oslot ogen fn2-pool)
    (mv code fn2-pool)))))
(defun fn2-rt-digits (n k)
 (declare (xargs :verify-guards nil :measure (nfix k)))
 (if (zp k) nil (append (fn2-rt-digits (floor n 10) (- k 1)) (list (+ 48 (mod n 10))))))
; Message-ID j: "<m" five digits "@t>"; fixed width, so byte order is j's order.
(defun fn2-rt-mid-octets (j)
 (declare (xargs :verify-guards nil))
 (append (list 60 109) (fn2-rt-digits j 5) (list 64 116 62)))
; Place OCTETS at the source cursor and point field row ROW at them.
(defun fn2-rt-set-octets (row octets slot gen off okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* (((mv code fn2-pool) (fn2-rt-write-bytes octets slot gen off okind oslot ogen fn2-pool))
      (fn2-fields (fn2-fields-set-ref-slot row slot fn2-fields))
      (fn2-fields (fn2-fields-set-ref-gen row gen fn2-fields))
      (fn2-fields (fn2-fields-set-ref-off row off fn2-fields))
      (fn2-fields (fn2-fields-set-ref-len row (len octets) fn2-fields)))
  (mv code (+ off (len octets)) fn2-fields fn2-pool)))
; Identity entry i: Message-ID floor(i/2), content bytes all (i mod 2),
; state accepted, article 100+i, binding i+1, principal 7.
(defun fn2-rt-mid-entry (i base slot gen off okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* (((mv & off fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ base *fn2-identity-entry-field-message-id*) (fn2-rt-mid-octets (floor i 2))
                          slot gen off okind oslot ogen fn2-fields fn2-pool))
      ((mv code off fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ base *fn2-identity-entry-field-content*) (make-list 32 :initial-element (mod i 2))
                          slot gen off okind oslot ogen fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-identity-entry-field-content*) 1 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-identity-entry-field-state*) *fn2-identity-state-accepted* fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-identity-entry-field-binding*) (+ 1 i) fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-identity-entry-field-principal*) 7 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-identity-entry-field-article*) (+ 100 i) fn2-fields)))
  (mv code off fn2-fields fn2-pool)))

(fn2-rt-defun fn2-rt-mid-add-loop (fuel i src sgen off)
 (if (zp fuel) (fn2-rt-mv :ok i off)
  (b* (((mv code off fn2-fields fn2-pool)
        (fn2-rt-mid-entry i *fn2-rt-entry-base* src sgen off 9 0 1 fn2-fields fn2-pool))
       ((unless (eq code :ok)) (fn2-rt-mv (list :source code) i off))
       ((mv code fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
        (fn2-run-add 0 1 *fn2-rt-entry-base* fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
   (if (eq code :ok) (fn2-rt-mid-add-loop (- fuel 1) (+ 1 i) src sgen off
                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-rt-mv code i off)))))

; Query (Message-ID j, content c) placed in a slot owned by a different owner
; (10 0 1): the compare reads the page and the query under their own owners.
(fn2-rt-defun fn2-rt-mid-seek (slot gen qslot qgen j c)
 (b* ((q *fn2-rt-query-base*) (rb *fn2-rt-reader-base*)
      ((mv & qoff fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ q *fn2-identity-entry-field-message-id*) (fn2-rt-mid-octets j) qslot qgen 0 10 0 1 fn2-fields fn2-pool))
      ((mv & & fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ q *fn2-identity-entry-field-content*) (make-list 32 :initial-element c) qslot qgen qoff 10 0 1 fn2-fields fn2-pool))
      ((mv code fn2-fields) (fn2-run-read-header slot gen rb 9 0 1 fn2-fields fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :header code)))
      ((mv code & & idx & fn2-fields)
       (fn2-run-seek 1 0 64 0 (fn2-run-hdr rb restarts) 0 0 q rb slot gen 9 0 1 10 0 1 fn2-fields fn2-pool))
      (article (if (eq code :found) (fn2-fields-value (+ rb *fn2-run-reader-entry* *fn2-identity-entry-field-article*) fn2-fields) nil)))
  (fn2-rt-mv (list code idx article))))
(fn2-rt-defun fn2-rt-mid-seeks (slot gen qslot qgen queries)
 (if (atom queries) (fn2-rt-mv nil)
  (b* (((mv one fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rt-mid-seek slot gen qslot qgen (caar queries) (cadar queries)
                         fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
       ((mv rest fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
        (fn2-rt-mid-seeks slot gen qslot qgen (cdr queries)
                          fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
   (fn2-rt-mv (cons one rest)))))

; N entries; then a repeated key (refused :order), close, head, seal, check,
; and the queries, after the source slot holding the keys is released.
(fn2-rt-defun fn2-rt-mid-page (n queries)
 (b* (((mv & fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-setup fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv & slot gen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((mv & src sgen fn2-pool) (fn2-pool-reserve 0 9 0 1 fn2-pool))
      ((mv & qslot qgen fn2-pool) (fn2-pool-reserve 1 10 0 1 fn2-pool))
      ((mv code fn2-run-writers fn2-pool)
       (fn2-run-open 0 slot gen 1 1 0 8 0 *page-kind-run-data* 6 2 4 1 1 9 0 1 *fn2-rt-writer-base* *fn2-run-page-size* fn2-run-writers fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :open code)))
      ((mv add count off fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-mid-add-loop n 0 src sgen 0 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv & & fn2-fields fn2-pool) (fn2-rt-mid-entry (- count 1) *fn2-rt-entry-base* src sgen off 9 0 1 fn2-fields fn2-pool))
      ((mv repeat fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
       (fn2-run-add 0 1 *fn2-rt-entry-base* fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      ((mv & fn2-run-writers) (fn2-run-close 0 fn2-run-writers))
      ((mv close fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-close 64 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv head fn2-run-writers fn2-fields fn2-pool) (fn2-run-head 0 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
      (fn2-fc-context (fn2-run-seal-context 0 0 *fn2-rt-hash-row* fn2-run-writers fn2-fc-context))
      ((mv seal fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-seal 64 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv check fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-check slot gen fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv released fn2-pool) (fn2-pool-release src sgen 9 0 1 fn2-pool))
      ((mv seeks fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-mid-seeks slot gen qslot qgen queries fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))
  (fn2-rt-mv (list :add add count :repeat repeat :close close :head head :seal seal :check check
                   :source-released released :seeks seeks))))
(defun fn2-rt-mid-page-result (n queries)
 (declare (xargs :verify-guards nil))
 (fn2-rt-with (fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
  (fn2-rt-mid-page n queries fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)))

; Scenario results (REPL-verified, now pinned).
(assert-event
 (equal (fn2-rt-num-page-result 300 '((1 2) (1 3) (1 600) (1 0) (1 601) (1 300) (0 9) (2 0)))
        '(:add :ok 300 :close :ok :head :ok :seal :ok :check :ok :restarts 19 :cursor 2690
          :seeks ((:found 0 100) (:absent 1 nil) (:found 299 399) (:absent 0 nil) (:absent 300 nil)
                  (:found 149 249) (:absent 0 nil) (:absent 300 nil))
          :flip :ok :bad-hash)))
; A full page: the 7,087th overview entry is refused :full; the page still
; seals, and its last entry (number 14,172) is found.
(assert-event
 (equal (fn2-rt-num-page-result 0 '((1 2) (1 14172) (1 14174)))
        '(:add :full 7086 :close :ok :head :ok :seal :ok :check :ok :restarts 443 :cursor 63764
          :seeks ((:found 0 100) (:found 7085 7185) (:absent 7086 nil))
          :flip :ok :bad-hash)))
; Identity-shaped keys: a repeated key is refused :order; lookups compare the
; sealed page's octets against a query held by another owner, after the source
; workspace holding the original keys was released.
(assert-event
 (equal (fn2-rt-mid-page-result 400 '((0 0) (0 1) (0 2) (199 1) (200 0) (57 0) (57 1) (100 7)))
        '(:add :ok 400 :repeat :order :close :ok :head :ok :seal :ok :check :ok :source-released :ok
          :seeks ((:found 0 100) (:found 1 101) (:absent 2 nil) (:found 399 499) (:absent 400 nil)
                  (:found 114 214) (:found 115 215) (:absent 202 nil)))))

(defconst *fn2-rt-num-meta* '(0 1 1 5 2 3 3 1 7 0 0))
(defconst *fn2-rt-num-key* '((group (:id group)) (number (:id group-number))))
(defun fn2-rt-num-entries (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- n i))))
 (if (zp (- n i)) nil
  (cons (list 1 (* 2 (+ 1 i)) (+ 100 i) (* 2 (+ 1 i)) (list 65)) (fn2-rt-num-entries (+ 1 i) n))))
; A query: (group number) with zero values.
(defun fn2-rt-nq (g n) (declare (xargs :verify-guards nil)) (list g n 0 0 nil))
(defconst *fn2-rt-num-good* (fn2-rt-num-entries 0 40))
(defconst *fn2-rt-num-bad* (append (list (nth 5 *fn2-rt-num-good*)) (take 5 *fn2-rt-num-good*) (nthcdr 6 *fn2-rt-num-good*)))
(fn2-rt-teeth fn2-overview 3 ((group (:id group)) (number (:id group-number)))
 *fn2-rt-num-meta* *fn2-rt-num-good* *fn2-rt-num-bad*
 (list (fn2-rt-nq 1 0) (fn2-rt-nq 1 2) (fn2-rt-nq 1 3) (fn2-rt-nq 1 33) (fn2-rt-nq 1 34) (fn2-rt-nq 1 80)
       (fn2-rt-nq 1 81) (fn2-rt-nq 0 99) (fn2-rt-nq 2 0))
 (fn2-rt-nq 1 40))

; Multi-page runs through the real build and lookup entry points. 3,000
; overview entries at a 400-byte fill: present, absent between, before and
; after; and a run of one entry.
(defconst *fn2-rt-num-3000* (fn2-rt-num-entries 0 3000))
(assert-event
 (equal (list (fn2-run-lookup-image 3 *fn2-overview-entry* *fn2-rt-num-3000* 400 (fn2-rt-nq 1 2))
              (fn2-run-lookup-image 3 *fn2-overview-entry* *fn2-rt-num-3000* 400 (fn2-rt-nq 1 6000))
              (fn2-run-lookup-image 3 *fn2-overview-entry* *fn2-rt-num-3000* 400 (fn2-rt-nq 1 3000))
              (fn2-run-lookup-image 3 *fn2-overview-entry* *fn2-rt-num-3000* 400 (fn2-rt-nq 1 3001))
              (fn2-run-lookup-image 3 *fn2-overview-entry* *fn2-rt-num-3000* 400 (fn2-rt-nq 1 6001))
              (fn2-run-lookup-image 3 *fn2-overview-entry* *fn2-rt-num-3000* 400 (fn2-rt-nq 0 9))
              (fn2-run-lookup-image 3 *fn2-overview-entry* (fn2-rt-num-entries 0 1) 400 (fn2-rt-nq 1 2))
              (fn2-run-lookup-image 3 *fn2-overview-entry* (fn2-rt-num-entries 0 1) 400 (fn2-rt-nq 1 4)))
        '((:found (1 2 100 2 (65))) (:found (1 6000 3099 6000 (65))) (:found (1 3000 1599 3000 (65))) (:absent nil)
          (:absent nil) (:absent nil) (:found (1 2 100 2 (65))) (:absent nil))))

; The keystones' premise fixes a fill at which every page holds two entries
; of the layout's largest size: 2,276 bytes for overview (a line holds up to
; 1,024 octets). Entries with 600-octet lines then fill three to a page, so
; 64 of them build a run of two levels.
(defun fn2-rt-wide-entries (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- n i))))
 (if (zp (- n i)) nil
  (cons (list 1 (* 2 (+ 1 i)) (+ 100 i) (* 2 (+ 1 i)) (make-list 600 :initial-element (+ 65 (mod i 26))))
        (fn2-rt-wide-entries (+ 1 i) n))))
(defconst *fn2-rt-num-64* (fn2-rt-wide-entries 0 64))
(defconst *fn2-rt-num-64-bad* (append (list (nth 5 *fn2-rt-num-64*)) (take 5 *fn2-rt-num-64*) (nthcdr 6 *fn2-rt-num-64*)))
(fn2-rt-run-teeth fn2-overview 3 ((group (:id group)) (number (:id group-number)))
 *fn2-rt-num-64* *fn2-rt-num-64-bad* 2276
 (list (fn2-rt-nq 1 2) (fn2-rt-nq 1 3) (fn2-rt-nq 1 64) (fn2-rt-nq 1 128) (fn2-rt-nq 1 129) (fn2-rt-nq 1 0)
       (fn2-rt-nq 0 7) (fn2-rt-nq 2 2))
 (fn2-rt-nq 1 40))

;; Glue teeth. Positive: the served assembly's schemas are assembled and every
;; function on their build and lookup path is guard-verified. Negative: a
;; schema carrying old per-schema glue admitted without guard verification
;; (as defrunschema once generated it) is refused by name, through the same
;; check.
(defun fn2-run-glue-verified-positive ()
 (declare (xargs :verify-guards nil))
 (and (subsetp-eq '(fn2-identity fn2-article fn2-overview fn2-addr) (strip-cars (fn2-run-glue-assembled)))
      (equal (fn2-run-glue-check (fn2-run-glue-assembled)) :ok)))
(defun fn2-rt-old-lookup-step (c budget)
 (declare (xargs :verify-guards nil))
 (list c budget))
(make-event
 (let ((snapshot (fn2-ra-glue-snapshot
                  (list (cons 'fn2-rt-old (list :id 902 :layouts '(fn2-overview-entry fn2-overview-index fn2-overview-run)
                                                :compare 'fn2-overview-compare)))
                  (w state))))
  (value `(defun fn2-run-glue-verified-negative ()
            (declare (xargs :verify-guards nil))
            (equal (fn2-run-glue-check ',snapshot) '(:unverified fn2-rt-old fn2-rt-old-lookup-step))))))
(fn2-assert-owed-teeth fn2-run-glue-verified)

;; Scans from a lower bound across pages and levels. 3,000 entries at a
;; 400-byte fill: from before the first, from the middle (present and absent
;; queries), and past the last.
(assert-event
 (let ((all *fn2-rt-num-3000*))
  (and (equal (fn2-run-scan-image 3 *fn2-overview-entry* all 400 (fn2-rt-nq 0 0) 3001) (append all (list :end)))
       (equal (fn2-run-scan-image 3 *fn2-overview-entry* all 400 (fn2-rt-nq 1 3000) 40) (fn2-run-scan-spec *fn2-rt-num-key* all (fn2-rt-nq 1 3000) 40))
       (equal (fn2-run-scan-image 3 *fn2-overview-entry* all 400 (fn2-rt-nq 1 3001) 2000) (fn2-run-scan-spec *fn2-rt-num-key* all (fn2-rt-nq 1 3001) 2000))
       (equal (fn2-run-scan-image 3 *fn2-overview-entry* all 400 (fn2-rt-nq 1 6001) 5) '(:end)))))
(fn2-rt-scan-teeth fn2-overview 3 ((group (:id group)) (number (:id group-number)))
 *fn2-rt-num-64* *fn2-rt-num-64-bad* 2276
 (list (list (fn2-rt-nq 0 0) 70) (list (fn2-rt-nq 1 3) 10) (list (fn2-rt-nq 1 64) 64) (list (fn2-rt-nq 1 128) 3)
       (list (fn2-rt-nq 1 129) 2) (list (fn2-rt-nq 1 40) 0))
 (fn2-rt-nq 1 0))

(fn2-rt-overlay-teeth fn2-overview 3 ((group (:id group)) (number (:id group-number)))
 (fn2-rt-shuffle *fn2-rt-num-good* 0 40) (cons (nth 3 *fn2-rt-num-good*) (fn2-rt-shuffle *fn2-rt-num-good* 0 40)))
