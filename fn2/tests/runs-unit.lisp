; Layer C1 unit: one run page written, sealed by B's sealer, accepted by B's
; checker, refused after a flipped byte, and searched by the generated seek.
(in-package "ACL2")
(include-book "../books/runs")
(include-book "std/util/bstar" :dir :system)

(defrunschema fn2-rt-num :id 900
 :key ((group (:id group)) (number (:id group-number)))
 :value ((article (:id article)))
 :merge :unique)

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

; Entry i of the numeric fixture: group 1, number 2(i+1), article 100+i.
(fn2-rt-defun fn2-rt-num-add-loop (fuel i)
 (if (zp fuel) (fn2-rt-mv :ok i)
  (b* ((e *fn2-rt-entry-base*)
       (fn2-fields (fn2-fields-set-value (+ e *fn2-rt-num-entry-field-group*) 1 fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ e *fn2-rt-num-entry-field-number*) (* 2 (+ 1 i)) fn2-fields))
       (fn2-fields (fn2-fields-set-value (+ e *fn2-rt-num-entry-field-article*) (+ 100 i) fn2-fields))
       ((mv code fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
        (fn2-rt-num-entry-add 0 e fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
   (if (eq code :ok) (fn2-rt-num-add-loop (- fuel 1) (+ 1 i)
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
      (fn2-fields (fn2-fields-set-value (+ q *fn2-rt-num-entry-field-group*) group fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ q *fn2-rt-num-entry-field-number*) number fn2-fields))
      ((mv code fn2-fields) (fn2-run-read-header slot gen rb 9 0 1 fn2-fields fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :header code)))
      ((mv code & & idx & fn2-fields)
       (fn2-rt-num-entry-seek 64 0 (fn2-run-hdr rb restarts) 0 0 q rb slot gen 9 0 1 9 0 1 fn2-fields fn2-pool))
      (article (if (eq code :found) (fn2-fields-value (+ rb *fn2-run-reader-entry* *fn2-rt-num-entry-field-article*) fn2-fields) nil)))
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
      ((mv code fn2-run-writers fn2-pool)
       (fn2-run-open 0 slot gen 900 1 0 7 0 *page-kind-run-data* 5 2 3 1 1 9 0 1 *fn2-rt-writer-base* *fn2-run-page-size* fn2-run-writers fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :open code)))
      ((mv add count fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-num-add-loop (if (zp n) 100000 n) 0 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
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

; The octet-keyed fixture: a Binding-shaped key (Message-ID octets, content
; digest), so one Message-ID with two contents is two adjacent entries.
(defrunschema fn2-rt-mid :id 901
 :key ((message-id (:octets 250)) (content :digest))
 :value ((article (:id article)))
 :merge :union)

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
; Entry i: Message-ID floor(i/2), content bytes all (i mod 2), article 100+i.
(defun fn2-rt-mid-entry (i base slot gen off okind oslot ogen fn2-fields fn2-pool)
 (declare (xargs :stobjs (fn2-fields fn2-pool) :verify-guards nil))
 (b* (((mv & off fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ base *fn2-rt-mid-entry-field-message-id*) (fn2-rt-mid-octets (floor i 2))
                          slot gen off okind oslot ogen fn2-fields fn2-pool))
      ((mv code off fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ base *fn2-rt-mid-entry-field-content*) (make-list 32 :initial-element (mod i 2))
                          slot gen off okind oslot ogen fn2-fields fn2-pool))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-rt-mid-entry-field-content*) 1 fn2-fields))
      (fn2-fields (fn2-fields-set-value (+ base *fn2-rt-mid-entry-field-article*) (+ 100 i) fn2-fields)))
  (mv code off fn2-fields fn2-pool)))

(fn2-rt-defun fn2-rt-mid-add-loop (fuel i src sgen off)
 (if (zp fuel) (fn2-rt-mv :ok i off)
  (b* (((mv code off fn2-fields fn2-pool)
        (fn2-rt-mid-entry i *fn2-rt-entry-base* src sgen off 9 0 1 fn2-fields fn2-pool))
       ((unless (eq code :ok)) (fn2-rt-mv (list :source code) i off))
       ((mv code fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
        (fn2-rt-mid-entry-add 0 *fn2-rt-entry-base* fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)))
   (if (eq code :ok) (fn2-rt-mid-add-loop (- fuel 1) (+ 1 i) src sgen off
                       fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
     (fn2-rt-mv code i off)))))

; Query (Message-ID j, content c) placed in a slot owned by a different owner
; (10 0 1): the compare reads the page and the query under their own owners.
(fn2-rt-defun fn2-rt-mid-seek (slot gen qslot qgen j c)
 (b* ((q *fn2-rt-query-base*) (rb *fn2-rt-reader-base*)
      ((mv & qoff fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ q *fn2-rt-mid-entry-field-message-id*) (fn2-rt-mid-octets j) qslot qgen 0 10 0 1 fn2-fields fn2-pool))
      ((mv & & fn2-fields fn2-pool)
       (fn2-rt-set-octets (+ q *fn2-rt-mid-entry-field-content*) (make-list 32 :initial-element c) qslot qgen qoff 10 0 1 fn2-fields fn2-pool))
      ((mv code fn2-fields) (fn2-run-read-header slot gen rb 9 0 1 fn2-fields fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :header code)))
      ((mv code & & idx & fn2-fields)
       (fn2-rt-mid-entry-seek 64 0 (fn2-run-hdr rb restarts) 0 0 q rb slot gen 9 0 1 10 0 1 fn2-fields fn2-pool))
      (article (if (eq code :found) (fn2-fields-value (+ rb *fn2-run-reader-entry* *fn2-rt-mid-entry-field-article*) fn2-fields) nil)))
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
       (fn2-run-open 0 slot gen 901 1 0 8 0 *page-kind-run-data* 6 2 4 1 1 9 0 1 *fn2-rt-writer-base* *fn2-run-page-size* fn2-run-writers fn2-pool))
      ((unless (eq code :ok)) (fn2-rt-mv (list :open code)))
      ((mv add count off fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests)
       (fn2-rt-mid-add-loop n 0 src sgen 0 fn2-run-writers fn2-run-restarts fn2-fields fn2-pool fn2-fc fn2-fc-context fn2-b3 fn2-digests))
      ((mv & & fn2-fields fn2-pool) (fn2-rt-mid-entry (- count 1) *fn2-rt-entry-base* src sgen off 9 0 1 fn2-fields fn2-pool))
      ((mv repeat fn2-run-writers fn2-run-restarts fn2-fields fn2-pool)
       (fn2-rt-mid-entry-add 0 *fn2-rt-entry-base* fn2-run-writers fn2-run-restarts fn2-fields fn2-pool))
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
        '(:add :ok 300 :close :ok :head :ok :seal :ok :check :ok :restarts 19 :cursor 1553
          :seeks ((:found 0 100) (:absent 1 nil) (:found 299 399) (:absent 0 nil) (:absent 300 nil)
                  (:found 149 249) (:absent 0 nil) (:absent 300 nil))
          :flip :ok :bad-hash)))
; A full page: the 11,788th entry is refused :full; the page still seals.
(assert-event
 (equal (fn2-rt-num-page-result 0 '((1 2) (1 20000) (1 20001)))
        '(:add :full 11787 :close :ok :head :ok :seal :ok :check :ok :restarts 737 :cursor 62584
          :seeks ((:found 0 100) (:found 9999 10099) (:absent 10000 nil))
          :flip :ok :bad-hash)))
; Identity-shaped keys: a repeated key is refused :order; lookups compare the
; sealed page's octets against a query held by another owner, after the source
; workspace holding the original keys was released.
(assert-event
 (equal (fn2-rt-mid-page-result 400 '((0 0) (0 1) (0 2) (199 1) (200 0) (57 0) (57 1) (100 7)))
        '(:add :ok 400 :repeat :order :close :ok :head :ok :seal :ok :check :ok :source-released :ok
          :seeks ((:found 0 100) (:found 1 101) (:absent 2 nil) (:found 399 499) (:absent 400 nil)
                  (:found 114 214) (:found 115 215) (:absent 202 nil)))))

;; Keystone teeth, one set per schema. Positive: the statement holds at an
;; inhabited premise (checked). Negative: without the premise (unsorted
;; entries, refused :order part way) the conclusion fails.
(defmacro fn2-rt-teeth (name key meta good bad queries badq)
 (let ((entry (fn2-columns-sym name "-ENTRY")))
  `(progn
    (defun ,(fn2-columns-sym name "-PAGE-ROUNDTRIP-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (fn2-run-page-inputp ,(fn2-codec-constant entry "") ',key ,meta ,good)
          (equal (,(fn2-columns-sym name "-PAGE-IMAGE") ,meta ,good)
                 (list :ok :ok :ok (fn2-run-page-spec ,(fn2-codec-constant entry "") ,meta ,good)))))
    (defun ,(fn2-columns-sym name "-PAGE-ROUNDTRIP-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (and (not (fn2-run-page-inputp ,(fn2-codec-constant entry "") ',key ,meta ,bad))
          (not (equal (,(fn2-columns-sym name "-PAGE-IMAGE") ,meta ,bad)
                      (list :ok :ok :ok (fn2-run-page-spec ,(fn2-codec-constant entry "") ,meta ,bad))))))
    (defun ,(fn2-columns-sym name "-SEEKS-HOLD") (qs)
     (declare (xargs :verify-guards nil))
     (or (atom qs)
         (and (fn2-run-values-layoutp ,(fn2-codec-constant entry "") (car qs))
              (equal (,(fn2-columns-sym name "-SEEK-IMAGE") ,meta ,good (car qs))
                     (fn2-run-lower-bound-spec ',key ,good (car qs) 0))
              (,(fn2-columns-sym name "-SEEKS-HOLD") (cdr qs)))))
    (defun ,(fn2-columns-sym name "-SEEK-LOWER-BOUND-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (,(fn2-columns-sym name "-SEEKS-HOLD") ,queries))
    (defun ,(fn2-columns-sym name "-SEEK-LOWER-BOUND-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (not (equal (,(fn2-columns-sym name "-SEEK-IMAGE") ,meta ,bad ,badq)
                 (fn2-run-lower-bound-spec ',key ,bad ,badq 0))))
    (fn2-assert-owed-teeth ,(fn2-columns-sym name "-PAGE-ROUNDTRIP") ,(fn2-columns-sym name "-SEEK-LOWER-BOUND")))))

(defconst *fn2-rt-num-meta* '(0 1 1 5 2 3 900 1 7 0 0))
(defun fn2-rt-num-entries (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- n i))))
 (if (zp (- n i)) nil (cons (list 1 (* 2 (+ 1 i)) (+ 100 i)) (fn2-rt-num-entries (+ 1 i) n))))
(defconst *fn2-rt-num-good* (fn2-rt-num-entries 0 40))
(defconst *fn2-rt-num-bad* (append (list (nth 5 *fn2-rt-num-good*)) (take 5 *fn2-rt-num-good*) (nthcdr 6 *fn2-rt-num-good*)))
(fn2-rt-teeth fn2-rt-num ((group (:id group)) (number (:id group-number)))
 *fn2-rt-num-meta* *fn2-rt-num-good* *fn2-rt-num-bad*
 '((1 0 0) (1 2 0) (1 3 0) (1 33 0) (1 34 0) (1 80 0) (1 81 0) (0 99 0) (2 0 0)) '(1 40 0))

(defconst *fn2-rt-mid-meta* '(0 1 1 6 2 4 901 1 8 0 0))
(defun fn2-rt-mid-entries (i n)
 (declare (xargs :verify-guards nil :measure (nfix (- n i))))
 (if (zp (- n i)) nil
  (cons (list (fn2-rt-mid-octets (floor i 2)) (cons 1 (make-list 32 :initial-element (mod i 2))) (+ 100 i))
        (fn2-rt-mid-entries (+ 1 i) n))))
(defconst *fn2-rt-mid-good* (fn2-rt-mid-entries 0 40))
(defconst *fn2-rt-mid-bad* (append (list (nth 5 *fn2-rt-mid-good*)) (take 5 *fn2-rt-mid-good*) (nthcdr 6 *fn2-rt-mid-good*)))
(fn2-rt-teeth fn2-rt-mid ((message-id (:octets 250)) (content :digest))
 *fn2-rt-mid-meta* *fn2-rt-mid-good* *fn2-rt-mid-bad*
 (list (list (fn2-rt-mid-octets 0) (cons 1 (make-list 32 :initial-element 0)) 0)
       (list (fn2-rt-mid-octets 7) (cons 1 (make-list 32 :initial-element 1)) 0)
       (list (fn2-rt-mid-octets 7) (cons 1 (make-list 32 :initial-element 2)) 0)
       (list (fn2-rt-mid-octets 19) (cons 1 (make-list 32 :initial-element 1)) 0)
       (list (fn2-rt-mid-octets 20) (cons 1 (make-list 32 :initial-element 0)) 0)
       (list nil (cons 1 (make-list 32 :initial-element 0)) 0))
 (nth 10 *fn2-rt-mid-good*))

; Multi-page runs through the real build and lookup entry points. 3,000
; numeric entries at a 400-byte fill: present, absent between, before and
; after; and a run of one entry.
(defconst *fn2-rt-num-3000* (fn2-rt-num-entries 0 3000))
(assert-event
 (equal (list (fn2-rt-num-run-lookup-image *fn2-rt-num-3000* 400 '(1 2 0))
              (fn2-rt-num-run-lookup-image *fn2-rt-num-3000* 400 '(1 6000 0))
              (fn2-rt-num-run-lookup-image *fn2-rt-num-3000* 400 '(1 3000 0))
              (fn2-rt-num-run-lookup-image *fn2-rt-num-3000* 400 '(1 3001 0))
              (fn2-rt-num-run-lookup-image *fn2-rt-num-3000* 400 '(1 6001 0))
              (fn2-rt-num-run-lookup-image *fn2-rt-num-3000* 400 '(0 9 0))
              (fn2-rt-num-run-lookup-image (fn2-rt-num-entries 0 1) 400 '(1 2 0))
              (fn2-rt-num-run-lookup-image (fn2-rt-num-entries 0 1) 400 '(1 4 0)))
        '((:found (1 2 100)) (:found (1 6000 3099)) (:found (1 3000 1599)) (:absent nil)
          (:absent nil) (:absent nil) (:found (1 2 100)) (:absent nil))))

; Run-lookup teeth. Positive: inhabited premise (checked), every query in a
; list agrees with the spec. Negative: without sortedness the conclusion fails.
(defmacro fn2-rt-run-teeth (name key good bad limit queries badq)
 (let ((entry (fn2-columns-sym name "-ENTRY")) (image (fn2-columns-sym name "-RUN-LOOKUP-IMAGE")))
  `(progn
    (defun ,(fn2-columns-sym name "-RUN-LOOKUPS-HOLD") (qs)
     (declare (xargs :verify-guards nil))
     (or (atom qs)
         (and (fn2-run-values-layoutp ,(fn2-codec-constant entry "") (car qs))
              (equal (,image ,good ,limit (car qs)) (fn2-run-key-lookup-spec ',key ,good (car qs)))
              (,(fn2-columns-sym name "-RUN-LOOKUPS-HOLD") (cdr qs)))))
    (defun ,(fn2-columns-sym name "-RUN-LOOKUP-EXACT-POSITIVE") ()
     (declare (xargs :verify-guards nil))
     (and (fn2-run-run-inputp ,(fn2-codec-constant entry "") ',key ,good ,limit)
          (,(fn2-columns-sym name "-RUN-LOOKUPS-HOLD") ,queries)))
    (defun ,(fn2-columns-sym name "-RUN-LOOKUP-EXACT-NEGATIVE") ()
     (declare (xargs :verify-guards nil))
     (and (not (fn2-run-run-inputp ,(fn2-codec-constant entry "") ',key ,bad ,limit))
          (not (equal (,image ,bad ,limit ,badq) (fn2-run-key-lookup-spec ',key ,bad ,badq)))))
    (fn2-assert-owed-teeth ,(fn2-columns-sym name "-RUN-LOOKUP-EXACT")))))
(defconst *fn2-rt-num-64* (fn2-rt-num-entries 0 64))
(fn2-rt-run-teeth fn2-rt-num ((group (:id group)) (number (:id group-number)))
 *fn2-rt-num-64* (append (list (nth 5 *fn2-rt-num-64*)) (take 5 *fn2-rt-num-64*) (nthcdr 6 *fn2-rt-num-64*)) 400
 '((1 2 0) (1 3 0) (1 64 0) (1 128 0) (1 129 0) (1 0 0) (0 7 0) (2 2 0)) '(1 40 0))
(fn2-rt-run-teeth fn2-rt-mid ((message-id (:octets 250)) (content :digest))
 *fn2-rt-mid-good* *fn2-rt-mid-bad* 1024
 (list (nth 0 *fn2-rt-mid-good*) (nth 17 *fn2-rt-mid-good*) (nth 39 *fn2-rt-mid-good*)
       (list (fn2-rt-mid-octets 7) (cons 1 (make-list 32 :initial-element 2)) 0)
       (list (fn2-rt-mid-octets 25) (cons 1 (make-list 32 :initial-element 0)) 0)
       (list nil (cons 1 (make-list 32 :initial-element 0)) 0))
 (nth 10 *fn2-rt-mid-good*))
