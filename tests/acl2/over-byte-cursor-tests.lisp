(in-package "ACL2")
(include-book "../../books/over-byte-invariants")

(defconst *obct-source*
  (append (fn-record-string-octets "Subject: a") '(13 10 32 98 13 10)
          (fn-record-string-octets "From: c") '(13 10)
          (fn-record-string-octets "Date: d") '(13 10)
          (fn-record-string-octets "Message-ID: <e@x>") '(13 10)
          (fn-record-string-octets "References: <r@x>") '(13 10 13 10 122 13 10)))

(defun obct-token ()
  (mv-let (owners pins status) (fn-rpin-step nil '(31 nil nil) '(:acquire 7))
    (declare (ignore pins status))
    (fn-rpin-token 7 owners)))

(defun obct-run (s fuel fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :measure (nfix fuel)
                  :verify-guards nil))
  (if (or (not s) (zp fuel)) (mv nil s t)
    (mv-let (out next) (fn-obc-one s fn-arena fn-cat)
      (mv-let (more final good) (obct-run next (1- fuel) fn-arena fn-cat)
        (mv (append out more) final
            (and good (fn-obc-statep s fn-arena)
                 (fn-cat-p fn-cat)
                 (fn-cat-handles-inp (fn-cat-count fn-cat) fn-arena fn-cat)
                 (fn-obc-source-ready-p s fn-arena fn-cat)
                 (fn-obc-cached-ready-p s fn-cat)
                 (or (not next) (fn-obc-statep next fn-arena))
                 (fn-cbor-octet-listp out) (<= (len out) 1)
                 (or (not next) (equal (nth 1 next) (nth 1 s)))))))))

(defun obct-case (legacy malformed fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat))
         (source (if malformed '(65 13 10 13 10) *obct-source*))
         (wire (fn-record-make 0 1 0 "<e@x>" source '("fn.test") "o" "s" "e" 1 5)))
    (mv-let (row fn-arena) (fn-cat-intern-list wire nil 0 fn-arena)
      (let* ((row (if legacy (fn-held-plain wire (fn-record-payload row)) row))
             (fn-cat (fn-cat-commit row fn-cat))
             (start (fn-obc-begin (fn-ovw-cursor "fn.test" 1 1 1 nil t) (obct-token))))
        (mv-let (bytes final good) (obct-run start 1000 fn-arena fn-cat)
          (mv (list bytes final good) fn-arena fn-cat))))))

(defconst *obct-expected*
  (append (fn-ovw-status (fn-proto-text * :overview))
          (fn-record-string-octets "1") '(9)
          (fn-record-string-octets "a b") '(9)
          (fn-record-string-octets "c") '(9)
          (fn-record-string-octets "d") '(9)
          (fn-record-string-octets "<e@x>") '(9)
          (fn-record-string-octets "<r@x>") '(9)
          (fn-nntp-decimal (len *obct-source*)) '(9 49 13 10 46 13 10)))

; Every actual intermediate state, complete row bytes and terminal framing.
; Positive witnesses for fn-obc-one-preserves-state-shape assert all three
; premises and its complete conclusion at every reached transition.
(assert-event
 (mv-let (r fn-arena fn-cat) (obct-case nil nil fn-arena fn-cat)
   (mv (and (equal (car r) *obct-expected*) (not (cadr r)) (caddr r)) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))
(assert-event
 (mv-let (r fn-arena fn-cat) (obct-case t nil fn-arena fn-cat)
   (mv (and (equal (car r) *obct-expected*) (not (cadr r)) (caddr r)) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))
(assert-event
 (mv-let (r fn-arena fn-cat) (obct-case nil t fn-arena fn-cat)
   (mv (and (equal (car r) (fn-ovw-status (fn-ovw-empty-text nil)))
            (not (cadr r)) (caddr r)) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))
(assert-event
 (mv-let (r fn-arena fn-cat) (obct-case t t fn-arena fn-cat)
   (mv (and (equal (car r) (fn-ovw-status (fn-ovw-empty-text nil)))
            (not (cadr r)) (caddr r)) fn-arena fn-cat))
 :stobjs-out '(nil fn-arena fn-cat))

; Literal saved-prefix theorem positives at each atomic quantum transition.
; This helper is only a bounded test driver, never a host implementation.
(defun obct-qsteps (q attempts fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :measure (nfix attempts)
                  :verify-guards nil))
  (if (or (zp attempts) (not (equal (fn-obc-quantum-status q) :continue)))
      (mv q t)
    (let ((next (fn-obc-quantum-one q fn-arena fn-cat)))
      (mv-let (next-bytes next-state) (fn-obc-quantum-finish next)
        (mv-let (old-bytes old-state) (fn-obc-quantum-finish q)
          (declare (ignore old-state))
          (mv-let (one-bytes one-state) (fn-obc-one (nth 0 q) fn-arena fn-cat)
            (mv-let (final good) (obct-qsteps next (1- attempts) fn-arena fn-cat)
              (mv final
                  (and good (true-listp q) (true-listp (nth 2 q))
                       (equal (fn-obc-quantum-status q) :continue)
                       (fn-obc-statep (nth 0 q) fn-arena)
                       (equal next-bytes (append old-bytes one-bytes))
                       (equal next-state one-state)
                       (equal (+ (nth 1 next) (nth 3 next))
                              (+ (nth 1 q) (nth 3 q)))
                       (<= (len (nth 2 next)) (+ 1 (len (nth 2 q)))))))))))))

(defun obct-split-case (legacy malformed quantum fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat))
         (source (if malformed '(65 13 10 13 10) *obct-source*))
         (wire (fn-record-make 0 1 0 "<e@x>" source '("fn.test") "o" "s" "e" 1 5)))
    (mv-let (row fn-arena) (fn-cat-intern-list wire nil 0 fn-arena)
      (let* ((row (if legacy (fn-held-plain wire (fn-record-payload row)) row))
             (fn-cat (fn-cat-commit row fn-cat))
             (start (fn-obc-begin (fn-ovw-cursor "fn.test" 1 1 1 nil t) (obct-token))))
        (mv-let (q good) (obct-qsteps (fn-obc-quantum-begin start quantum)
                                    quantum fn-arena fn-cat)
          (mv-let (prefix next) (fn-obc-quantum-finish q)
            (mv-let (suffix final rest-good) (obct-run next 1000 fn-arena fn-cat)
              (mv (and good rest-good (not final)
                       (equal (append prefix suffix)
                              (if malformed (fn-ovw-status (fn-ovw-empty-text nil))
                                *obct-expected*))
                       (or (not next) (equal (nth 1 next) (obct-token))))
                  fn-arena fn-cat))))))))

; Split while seeking, partway through the 224 line, within a legacy
; header, and after parsing. Every resumed suffix starts at saved NEXT.
(assert-event
 (mv-let (good fn-arena fn-cat) (obct-split-case nil nil 1 fn-arena fn-cat)
   (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
(assert-event
 (mv-let (good fn-arena fn-cat) (obct-split-case nil nil 7 fn-arena fn-cat)
   (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
(assert-event
 (mv-let (good fn-arena fn-cat) (obct-split-case t nil 7 fn-arena fn-cat)
   (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
(assert-event
 (mv-let (good fn-arena fn-cat) (obct-split-case t nil 110 fn-arena fn-cat)
   (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))
(assert-event
 (mv-let (good fn-arena fn-cat) (obct-split-case t t 7 fn-arena fn-cat)
   (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))

; Corrupted-state witness, cached-ready hypothesis removed. The five-field
; column has a non-string subject while its valid/tomb flags still select
; emission. The other two literal hypotheses hold; the conclusion fails.
(defun obct-corrupt-column (fn-arena fn-cat)
  (declare (xargs :stobjs (fn-arena fn-cat) :verify-guards nil))
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat))
         (wire (fn-record-make 0 1 0 "<e@x>" *obct-source*
                               '("fn.test") "o" "s" "e" 1 5)))
    (mv-let (row fn-arena) (fn-cat-intern-list wire nil 0 fn-arena)
      (let* ((facts (fn-held-facts row))
             (nov (fn-hf-nov facts))
             (broken (fn-hnov-make nil t 7 (fn-hnov-from nov)
                                   (fn-hnov-date nov) (fn-hnov-msgid nov)
                                   (fn-hnov-references nov)))
             (facts (fn-hf-make (fn-hf-octets facts) (fn-hf-body-start facts)
                               (fn-hf-body-lines facts)
                               (list nil nil nil broken)))
             (row (update-nth 11 facts row))
             (fn-cat (fn-cat-commit row fn-cat))
             (s (fn-obc-begin (fn-ovw-cursor "fn.test" 1 1 1 nil t) (obct-token))))
        (mv-let (out next) (fn-obc-one s fn-arena fn-cat)
          (declare (ignore out))
          (mv (and (fn-obc-statep s fn-arena)
                   (fn-obc-source-ready-p s fn-arena fn-cat)
                   (not (fn-obc-cached-ready-p s fn-cat))
                   next (not (fn-obc-statep next fn-arena)))
              fn-arena fn-cat))))))

(assert-event
 (mv-let (good fn-arena fn-cat) (obct-corrupt-column fn-arena fn-cat)
   (mv good fn-arena fn-cat)) :stobjs-out '(nil fn-arena fn-cat))

; Corrupted-state removal of the maintained state shape: an absent pin
; survives into a terminal emission. Both selected-row premises hold.
(assert-event
 (with-guard-checking :none
  (let* ((fn-arena (fn-arena-clear fn-arena)) (fn-cat (fn-cat-clear fn-cat))
        (s (fn-obc-begin (fn-ovw-cursor "fn.test" 1 0 0 nil t) nil)))
   (mv-let (out next) (fn-obc-one s fn-arena fn-cat)
     (declare (ignore out))
     (mv (and (not (fn-obc-statep s fn-arena))
              (fn-obc-source-ready-p s fn-arena fn-cat)
              (fn-obc-cached-ready-p s fn-cat)
              next (not (fn-obc-statep next fn-arena)))
         fn-arena fn-cat)))) :stobjs-out '(nil fn-arena fn-cat))

; Corrupted-state removal of source-ready in the logical representation.
; A live abstract stobj refuses an out-of-range primitive even with guard
; checking disabled, so this explicit conjunction is proved over the empty
; logical arena and a one-row logical catalog, rather than executed live.
(defthm obct-source-ready-removal
  (let* ((fn-arena nil)
         (wire (fn-record-make 0 1 0 "<e@x>" nil '("fn.test") "o" "s" "e" 1 5))
         (fn-cat (list (fn-held-with-numbers (fn-held-plain wire 1)
                                            '(("fn.test" . 1)))))
         (s (fn-obc-begin (fn-ovw-cursor "fn.test" 1 1 1 nil t) (obct-token)))
         (next (mv-nth 1 (fn-obc-one s fn-arena fn-cat))))
    (and (fn-obc-statep s fn-arena)
         (not (fn-obc-source-ready-p s fn-arena fn-cat))
         (fn-obc-cached-ready-p s fn-cat)
         next (not (fn-obc-statep next fn-arena))))
  :rule-classes nil
  :hints (("Goal" :in-theory
           (enable fn-arena-count-is-len fn-arena-payload-len-is-len-nth
                   fn-cat-count-is-len fn-cat-at-is-nth
                   fn-cat-group-number-is-number-seq fn-obc-one fn-obc-statep
                   fn-obc-source-ready-p fn-obc-cached-ready-p fn-cnx-view-seq))))
