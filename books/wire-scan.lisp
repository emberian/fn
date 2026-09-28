; fn: the wire machine over a span of the octet buffer, a line at a time
; (D27; REP-012; PKT-479).
;
; books/wire-span.lisp fn-wire-span-fold reads the buffer in place but still
; steps fn-wire-feed-byte once per octet: a new eight-cell wire state and a
; two-cell result per octet, and books/served-span.lisp rebuilt the twelve-
; field connection around each of them (lane post-alloc: ~1.1 MB of a 2.2 MB
; owner POST of 2 KiB).  fn-wire-scan is the same fold with the run of
; ordinary octets inside a line taken in one step: fn-wscan-plain-end finds
; the next CR, LF, non-octet or line-limit position by index, allocating
; nothing, and fn-wscan-revonto conses the run onto the retained partial line
; (the only allocation per octet: one cons, the model's line-rev).  CR, LF, a
; refusal and the line end still go through fn-wire-feed-byte itself, so the
; framing, the dot rule and every limit are the reference machine's.
; A WHOLE line inside the range (an empty retained line, the run, CR LF) is
; built forward from the buffer (fn-wscan-slice-onto, one cons per octet) and
; handed to fn-wire-after-line directly, instead of consed onto line-rev and
; reversed at LF (two conses per octet; lane input-loop-2, item 4).
;
; KEYSTONE fn-wire-scan-is-span-fold (no hypothesis): the scan IS
; fn-wire-span-fold (state, events and the next index), hence, by
; books/wire-span.lisp fn-wire-span-fold-is-feed-proper, fn-wire-feed-proper
; over the octets it consumed.  Called from books/served-scan.lisp
; fn-scar-scan-span, the executable of fn-scar-feed-span at
; books/served-span.lisp fn-scar-step-span-core.

(in-package "ACL2")
(include-book "wire-span")
(include-book "body-chunks-span")
(local (include-book "arithmetic/top" :dir :system))

; -----------------------------------------------------------------------------
; The run of ordinary octets from I: the first index K >= I that is END, or
; where the line would exceed its limit (LEN counts the line so far), or whose
; octet is CR, LF or not an octet.  Reads the buffer; allocates nothing.

(defun fn-wscan-ordinaryp (b)
  (declare (xargs :guard t))
  (and (fn-wire-octetp b) (not (equal b 13)) (not (equal b 10))))

(defun fn-wscan-plain-end (i end len limit fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets))
                              (natp len) (natp limit))
                  :measure (nfix (- end i))))
  (if (or (not (natp i)) (not (natp end)) (>= i end)
          (not (natp len)) (not (natp limit)) (>= len limit)
          (not (fn-wscan-ordinaryp (fn-octets-get i fn-octets))))
      (nfix i)
    (fn-wscan-plain-end (+ 1 i) end (+ 1 len) limit fn-octets)))

(defthm fn-wscan-plain-end-bounds
  (implies (and (natp i) (natp end) (<= i end))
           (and (<= i (fn-wscan-plain-end i end len limit fn-octets))
                (<= (fn-wscan-plain-end i end len limit fn-octets) end)))
  :rule-classes :linear)

(defthm fn-wscan-plain-end-natp
  (natp (fn-wscan-plain-end i end len limit fn-octets))
  :rule-classes :type-prescription)

(defthm fn-wscan-plain-end-advances
  (implies (and (natp i) (natp end) (< i end) (natp len) (natp limit)
                (< len limit)
                (fn-wscan-ordinaryp (fn-octets-get i fn-octets)))
           (< i (fn-wscan-plain-end i end len limit fn-octets)))
  :rule-classes :linear)

; The run's octets consed onto ACC in arrival order (the last octet first),
; which is what fn-wire-feed-byte does to line-rev one octet at a time.
; Tail recursive: a line as long as the profile admits takes no stack.
(defun fn-wscan-revonto (i k acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp k) (<= i k)
                              (<= k (fn-octets-len fn-octets)))
                  :measure (nfix (- k i))))
  (if (or (not (natp i)) (not (natp k)) (>= i k))
      acc
    (fn-wscan-revonto (+ 1 i) k (cons (fn-octets-get i fn-octets) acc)
                      fn-octets)))

(defthm fn-wscan-revonto-empty
  (equal (fn-wscan-revonto i i acc fn-octets) acc)
  :hints (("Goal" :expand ((fn-wscan-revonto i i acc fn-octets)))))

(defthm fn-wscan-revonto-step
  (implies (and (natp i) (natp k) (< i k))
           (equal (fn-wscan-revonto i k acc fn-octets)
                  (fn-wscan-revonto (+ 1 i) k (cons (fn-octets-get i fn-octets) acc)
                                    fn-octets)))
  :hints (("Goal" :expand ((fn-wscan-revonto i k acc fn-octets)))))

; The wire state after the run [I, K): the reference state after K - I
; ordinary octets, built once.  In article mode the run goes into the body's
; store straight from the buffer (books/body-chunks-span.lisp: packed a block
; at a time, no list of it built); in command mode it is consed onto the line.
(defun fn-wscan-after-run (wire-state i k fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep wire-state)
                              (natp i) (natp k) (<= i k)
                              (<= k (fn-octets-len fn-octets)))))
  (if (equal (fn-wire-state-mode wire-state) :article)
      (fn-wire-make-state :article nil
                          (+ (fn-wire-state-line-len wire-state) (- k i))
                          (fn-bchs-push-span (fn-wire-state-body-rev wire-state) i k fn-octets)
                          nil
                          (fn-wire-state-body-size wire-state)
                          (fn-wire-state-line-limit wire-state)
                          (fn-wire-state-body-limit wire-state))
    (fn-wire-make-state (fn-wire-state-mode wire-state)
                        (fn-wscan-revonto i k (fn-wire-state-line-rev wire-state)
                                          fn-octets)
                        (+ (fn-wire-state-line-len wire-state) (- k i))
                        (fn-wire-state-body-rev wire-state)
                        nil
                        (fn-wire-state-body-size wire-state)
                        (fn-wire-state-line-limit wire-state)
                        (fn-wire-state-body-limit wire-state))))

; Whether the octet at I starts a run: an open wire with no pending CR, room
; on the line, and an ordinary octet -- but not an article line's leading
; dot, which the byte step counts and drops.
(defun fn-wscan-runp (wire-state i fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep wire-state)
                              (natp i) (< i (fn-octets-len fn-octets)))))
  (and (not (equal (fn-wire-state-mode wire-state) :closed))
       (not (equal (fn-wire-state-pending-crp wire-state) t))
       (natp (fn-wire-state-line-len wire-state))
       (natp (fn-wire-state-line-limit wire-state))
       (< (fn-wire-state-line-len wire-state)
          (fn-wire-state-line-limit wire-state))
       (fn-wscan-ordinaryp (fn-octets-get i fn-octets))
       (not (and (equal (fn-wire-state-mode wire-state) :article)
                 (equal (fn-wire-state-line-len wire-state) 0)
                 (equal (fn-octets-get i fn-octets) 46)))))

(local
 (defthm fn-wscan-plain-end-within-limit
   (implies (and (natp i) (natp len) (natp limit) (<= len limit))
            (<= (+ len (- (fn-wscan-plain-end i end len limit fn-octets) i))
                limit))
   :rule-classes :linear))

(defthm fn-wscan-after-run-fast-statep
  (implies (and (fn-wire-fast-statep wire-state)
                (natp i) (natp k) (<= i k)
                (<= (+ (fn-wire-state-line-len wire-state) (- k i))
                    (fn-wire-state-line-limit wire-state))
                (not (equal (fn-wire-state-mode wire-state) :closed)))
           (fn-wire-fast-statep (fn-wscan-after-run wire-state i k fn-octets)))
  :hints (("Goal" :in-theory (e/d (fn-wire-fast-statep fn-wscan-after-run)
                                  (fn-wscan-revonto)))))

(defthm fn-wscan-after-plain-run-fast-statep
  (implies (and (fn-wire-fast-statep wire-state)
                (not (equal (fn-wire-state-mode wire-state) :closed))
                (natp i) (natp end) (<= i end))
           (fn-wire-fast-statep
            (fn-wscan-after-run
             wire-state i
             (fn-wscan-plain-end i end (fn-wire-state-line-len wire-state)
                                 (fn-wire-state-line-limit wire-state)
                                 fn-octets)
             fn-octets)))
  :hints (("Goal"
           :in-theory (disable fn-wscan-after-run fn-wscan-plain-end
                               fn-wscan-after-run-fast-statep
                               fn-wscan-plain-end-within-limit)
           :use ((:instance fn-wscan-after-run-fast-statep
                            (k (fn-wscan-plain-end
                                i end (fn-wire-state-line-len wire-state)
                                (fn-wire-state-line-limit wire-state)
                                fn-octets)))
                 (:instance fn-wscan-plain-end-within-limit
                            (len (fn-wire-state-line-len wire-state))
                            (limit (fn-wire-state-line-limit wire-state)))))
          (and stable-under-simplificationp
               '(:in-theory (e/d (fn-wire-fast-statep)
                                 (fn-wscan-after-run fn-wscan-plain-end
                                  fn-wscan-after-run-fast-statep
                                  fn-wscan-plain-end-within-limit))))))

;; -----------------------------------------------------------------------------
;; A whole line inside the range (item 4 of lane input-loop-2).  When the
;; retained partial line is empty and the run [I, K) is followed by CR LF
;; inside the range, the completed line is built FORWARD from the buffer, one
;; cons per octet, and handed to fn-wire-after-line: the reference conses the
;; run onto line-rev and then reverses it at LF, two conses per octet.

; Octets [I, K) consed onto ACC in order (the octet at I first), from the
; last down: tail recursive, one cons per octet.
(defun fn-wscan-slice-onto (i k acc fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (natp i) (natp k) (<= i k)
                              (<= k (fn-octets-len fn-octets)))
                  :measure (nfix (- k i))))
  (if (or (not (natp i)) (not (natp k)) (>= i k))
      acc
    (fn-wscan-slice-onto i (- k 1) (cons (fn-octets-get (- k 1) fn-octets) acc)
                         fn-octets)))

; Whether the octets from I are a whole line the scan takes at once: a run
; (fn-wscan-runp) onto an EMPTY retained line, ending at K with CR LF at K and
; K + 1, both inside the range.
(defun fn-wscan-linep (wire-state i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep wire-state)
                              (natp i) (natp end) (< i end)
                              (<= end (fn-octets-len fn-octets)))))
  (and (fn-wscan-runp wire-state i fn-octets)
       (null (fn-wire-state-line-rev wire-state))
       (let ((k (fn-wscan-plain-end i end (fn-wire-state-line-len wire-state)
                                    (fn-wire-state-line-limit wire-state)
                                    fn-octets)))
         (and (< (+ 1 k) end)
              (equal (fn-octets-get k fn-octets) 13)
              (equal (fn-octets-get (+ 1 k) fn-octets) 10)))))

(defthm fn-wscan-after-line-fast-statep
  (implies (fn-wire-fast-statep wire-state)
           (fn-wire-fast-statep
            (fn-wire-result-state (fn-wire-after-line wire-state line))))
  :hints (("Goal" :in-theory (enable fn-wire-after-line fn-wire-close
                                     fn-wire-fast-statep))))

(defthm fn-wscan-linep-line-ends-inside
  (implies (fn-wscan-linep wire-state i end fn-octets)
           (< (+ 1 (fn-wscan-plain-end i end (fn-wire-state-line-len wire-state)
                                       (fn-wire-state-line-limit wire-state)
                                       fn-octets))
              end))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-wscan-linep))))

(in-theory (disable fn-wscan-after-run fn-wscan-runp fn-wscan-linep))

; -----------------------------------------------------------------------------
; The scan.  A closed wire consumes the rest of the range and yields nothing,
; as the byte fold does after walking it.

(defun fn-wire-scan (wire-state i end fn-octets)
  (declare (xargs :stobjs fn-octets
                  :guard (and (fn-wire-fast-statep wire-state)
                              (natp i) (natp end) (<= i end)
                              (<= end (fn-octets-len fn-octets)))
                  :measure (nfix (- end i))
                  :verify-guards nil
                  :hints (("Goal" :in-theory (enable fn-wscan-runp fn-wscan-linep)))))
  (cond ((or (not (natp i)) (not (natp end)) (>= i end))
         (fn-wsp-make wire-state nil (nfix i)))
        ((equal (fn-wire-state-mode wire-state) :closed)
         (fn-wsp-make wire-state nil end))
        ((fn-wscan-linep wire-state i end fn-octets)
         (let* ((k (fn-wscan-plain-end i end (fn-wire-state-line-len wire-state)
                                       (fn-wire-state-line-limit wire-state)
                                       fn-octets))
                (r (if (equal (fn-wire-state-mode wire-state) :article)
                       (fn-wire-after-line (fn-wscan-after-run wire-state i k fn-octets) nil)
                     (fn-wire-after-line wire-state
                                         (fn-wscan-slice-onto i k nil fn-octets)))))
           (if (consp (fn-wire-result-events r))
               (fn-wsp-make (fn-wire-result-state r) (fn-wire-result-events r)
                            (+ 2 k))
             (fn-wire-scan (fn-wire-result-state r) (+ 2 k) end fn-octets))))
        ((fn-wscan-runp wire-state i fn-octets)
         (let ((k (fn-wscan-plain-end i end (fn-wire-state-line-len wire-state)
                                      (fn-wire-state-line-limit wire-state)
                                      fn-octets)))
           (fn-wire-scan (fn-wscan-after-run wire-state i k fn-octets)
                         k end fn-octets)))
        (t
         (let ((r (fn-wire-feed-byte wire-state (fn-octets-get i fn-octets))))
           (if (consp (fn-wire-result-events r))
               (fn-wsp-make (fn-wire-result-state r) (fn-wire-result-events r)
                            (+ 1 i))
             (fn-wire-scan (fn-wire-result-state r) (+ 1 i) end fn-octets))))))

(defthm fn-wire-scan-preserves-fast-statep
  (implies (fn-wire-fast-statep wire-state)
           (fn-wire-fast-statep
            (fn-wsp-state (fn-wire-scan wire-state i end fn-octets))))
  :hints (("Goal" :induct (fn-wire-scan wire-state i end fn-octets)
           :in-theory (disable fn-wire-feed-byte fn-wire-fast-statep))))

(verify-guards fn-wire-scan
  :hints (("Goal" :in-theory (e/d (fn-wscan-runp fn-wscan-linep)
                                  (fn-wire-feed-byte fn-wire-fast-statep
                                   fn-wire-after-line)))))

(defthm fn-wire-scan-next-bounds
  (implies (and (natp i) (natp end) (< i end))
           (and (< i (fn-wsp-next (fn-wire-scan wire-state i end fn-octets)))
                (<= (fn-wsp-next (fn-wire-scan wire-state i end fn-octets))
                    end)))
  :rule-classes :linear
  :hints (("Goal" :induct (fn-wire-scan wire-state i end fn-octets)
           :in-theory (e/d (fn-wscan-runp) (fn-wire-feed-byte fn-wire-after-line)))))

(defthm fn-wire-scan-next-natp
  (natp (fn-wsp-next (fn-wire-scan wire-state i end fn-octets)))
  :rule-classes :type-prescription
  :hints (("Goal" :induct (fn-wire-scan wire-state i end fn-octets)
           :in-theory (disable fn-wire-feed-byte fn-wire-after-line))))

; -----------------------------------------------------------------------------
; The correspondence.

(local
 (defthm fn-wscan-true-list-of-len-zero
   (implies (and (true-listp y) (equal (len y) 0))
            (equal y nil))
   :rule-classes :forward-chaining))

(local
 (defthm fn-wscan-make-state-of-fields
   (implies (fn-wire-state-shapep x)
            (equal (fn-wire-make-state (fn-wire-state-mode x)
                                       (fn-wire-state-line-rev x)
                                       (fn-wire-state-line-len x)
                                       (fn-wire-state-body-rev x)
                                       (fn-wire-state-pending-crp x)
                                       (fn-wire-state-body-size x)
                                       (fn-wire-state-line-limit x)
                                       (fn-wire-state-body-limit x))
                   x))
   :hints (("Goal" :in-theory (enable fn-wire-state-shapep fn-wire-make-state
                                      fn-wire-state-mode fn-wire-state-line-rev
                                      fn-wire-state-line-len fn-wire-state-body-rev
                                      fn-wire-state-pending-crp
                                      fn-wire-state-body-size
                                      fn-wire-state-line-limit
                                      fn-wire-state-body-limit
                                      fn-wire-ag-car fn-wire-ag-cdr)
            :expand ((len x) (len (cdr x)) (len (cddr x)) (len (cdddr x))
                     (len (cddddr x)) (len (cdr (cddddr x)))
                     (len (cddr (cddddr x))) (len (cdddr (cddddr x))))))))

(local
 (defthm fn-wscan-make-state-of-fields-no-cr
   (implies (and (fn-wire-state-shapep x)
                 (not (fn-wire-state-pending-crp x)))
            (equal (fn-wire-make-state (fn-wire-state-mode x)
                                       (fn-wire-state-line-rev x)
                                       (fn-wire-state-line-len x)
                                       (fn-wire-state-body-rev x)
                                       nil
                                       (fn-wire-state-body-size x)
                                       (fn-wire-state-line-limit x)
                                       (fn-wire-state-body-limit x))
                   x))
   :hints (("Goal" :use fn-wscan-make-state-of-fields))))

; One ordinary octet through the reference step: fn-wire-take-octet, no
; event.
(local
 (defthm fn-wscan-feed-byte-ordinary
   (implies (and (not (equal (fn-wire-state-mode wire-state) :closed))
                 (not (equal (fn-wire-state-pending-crp wire-state) t))
                 (< (fn-wire-state-line-len wire-state)
                    (fn-wire-state-line-limit wire-state))
                 (fn-wscan-ordinaryp byte))
            (equal (fn-wire-feed-byte wire-state byte)
                   (fn-wire-make-result (fn-wire-take-octet wire-state byte) nil)))
   :hints (("Goal" :in-theory (enable fn-wire-feed-byte)))))

; The run's first octet taken by the byte step, the rest by the run.
(local
 (defthm fn-wscan-after-run-step
   (implies (and (fn-wscan-runp ws i fn-octets)
                 (natp i) (natp k) (< i k))
            (equal (fn-wscan-after-run (fn-wire-take-octet ws (fn-octets-get i fn-octets))
                                       (+ 1 i) k fn-octets)
                   (fn-wscan-after-run ws i k fn-octets)))
   :hints (("Goal" :in-theory (e/d (fn-wscan-runp fn-wscan-after-run fn-wire-take-octet)
                                   (fn-wscan-ordinaryp))
                   :expand ((fn-bchs-slice i k fn-octets))))))

(local
 (defthm fn-wscan-after-run-empty-fields
   (implies (and (natp (fn-wire-state-line-len ws))
                 (or (not (equal (fn-wire-state-mode ws) :article))
                     (null (fn-wire-state-line-rev ws))))
            (equal (fn-wscan-after-run ws i i fn-octets)
                   (fn-wire-make-state (fn-wire-state-mode ws)
                                       (fn-wire-state-line-rev ws)
                                       (fn-wire-state-line-len ws)
                                       (fn-wire-state-body-rev ws)
                                       nil
                                       (fn-wire-state-body-size ws)
                                       (fn-wire-state-line-limit ws)
                                       (fn-wire-state-body-limit ws))))
   :hints (("Goal" :in-theory (enable fn-wscan-after-run)))))

(local
 (defthm fn-wscan-after-run-empty
   (implies (and (fn-wire-state-shapep ws)
                 (not (fn-wire-state-pending-crp ws))
                 (natp (fn-wire-state-line-len ws))
                 (or (not (equal (fn-wire-state-mode ws) :article))
                     (null (fn-wire-state-line-rev ws))))
            (equal (fn-wscan-after-run ws i i fn-octets) ws))
   :hints (("Goal" :in-theory (disable fn-wscan-after-run-empty-fields)
                   :use ((:instance fn-wscan-after-run-empty-fields)
                         (:instance fn-wscan-make-state-of-fields-no-cr (x ws)))))))

(local
 (defthm fn-wscan-take-octet-shape
   (and (fn-wire-state-shapep (fn-wire-take-octet ws x))
        (not (fn-wire-state-pending-crp (fn-wire-take-octet ws x)))
        (equal (fn-wire-state-mode (fn-wire-take-octet ws x))
               (fn-wire-state-mode ws))
        (equal (fn-wire-state-line-len (fn-wire-take-octet ws x))
               (+ 1 (fn-wire-state-line-len ws)))
        (equal (fn-wire-state-line-limit (fn-wire-take-octet ws x))
               (fn-wire-state-line-limit ws))
        (equal (fn-wire-state-line-rev (fn-wire-take-octet ws x))
               (if (equal (fn-wire-state-mode ws) :article)
                   nil
                 (cons x (fn-wire-state-line-rev ws)))))
   :hints (("Goal" :in-theory (enable fn-wire-take-octet)))))

(local
 (defthm fn-wscan-after-run-one
   (implies (and (fn-wscan-runp ws i fn-octets) (natp i)
                 (equal k (+ 1 i)))
            (equal (fn-wscan-after-run ws i k fn-octets)
                   (fn-wire-take-octet ws (fn-octets-get i fn-octets))))
   :hints (("Goal" :use ((:instance fn-wscan-after-run-step (k (+ 1 i)))
                         (:instance fn-wscan-after-run-empty
                                    (ws (fn-wire-take-octet ws (fn-octets-get i fn-octets)))
                                    (i (+ 1 i))))
                   :in-theory (e/d (fn-wscan-runp)
                                   (fn-wscan-after-run-step fn-wscan-after-run-empty
                                    fn-wscan-after-run fn-wire-take-octet))))))

; The induction for the run: the octet index and the wire state move
; together, a byte step at a time.
(local
 (defun fn-wscan-run-ind (ws i end fn-octets)
   (declare (xargs :stobjs fn-octets :measure (nfix (- end i))
                   :verify-guards nil))
   (if (or (not (natp i)) (not (natp end)) (>= i end)
           (not (fn-wscan-runp ws i fn-octets)))
       (list ws i end)
     (fn-wscan-run-ind (fn-wire-take-octet ws (fn-octets-get i fn-octets))
                       (+ 1 i) end fn-octets))))

(local
 (defthm fn-wscan-plain-end-step-back
   (implies (and (natp i) (natp end) (< i end) (natp len) (natp limit) (< len limit)
                 (fn-wscan-ordinaryp (fn-octets-get i fn-octets)))
            (equal (fn-wscan-plain-end (+ 1 i) end (+ 1 len) limit fn-octets)
                   (fn-wscan-plain-end i end len limit fn-octets)))
   :hints (("Goal" :expand ((fn-wscan-plain-end i end len limit fn-octets))))))

(local
 (defthm fn-wscan-plain-end-one
   (implies (and (natp i) (natp end) (< i end) (natp len) (natp limit) (< len limit)
                 (fn-wscan-ordinaryp (fn-octets-get i fn-octets))
                 (or (<= end (+ 1 i)) (<= limit (+ 1 len))
                     (not (fn-wscan-ordinaryp (fn-octets-get (+ 1 i) fn-octets)))))
            (equal (fn-wscan-plain-end i end len limit fn-octets)
                   (+ 1 i)))
   :hints (("Goal" :expand ((fn-wscan-plain-end i end len limit fn-octets)
                            (fn-wscan-plain-end (+ 1 i) end (+ 1 len) limit fn-octets))))))

(local
 (defthm fn-wscan-plain-end-stops
   (implies (and (natp i) (natp end) (natp len) (natp limit)
                 (or (>= i end) (>= len limit)
                     (not (fn-wscan-ordinaryp (fn-octets-get i fn-octets)))))
            (equal (fn-wscan-plain-end i end len limit fn-octets) i))
   :hints (("Goal" :expand ((fn-wscan-plain-end i end len limit fn-octets))))))

(local
 (defthm fn-wscan-span-fold-over-run-any
   (implies (and (fn-wscan-runp ws i fn-octets)
                 (natp i) (natp end) (< i end))
            (equal (fn-wire-span-fold
                    (fn-wscan-after-run
                     ws i
                     (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                         (fn-wire-state-line-limit ws)
                                         fn-octets)
                     fn-octets)
                    (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                        (fn-wire-state-line-limit ws)
                                        fn-octets)
                    end fn-octets)
                   (fn-wire-span-fold ws i end fn-octets)))
   :hints (("Goal" :induct (fn-wscan-run-ind ws i end fn-octets)
            :in-theory (e/d ()
                            (fn-wire-feed-byte fn-wscan-ordinaryp fn-wire-take-octet
                             fn-wscan-plain-end fn-oct-get-is-nth))
            :expand ((fn-wire-span-fold ws i end fn-octets)))

           (and stable-under-simplificationp
                '(:in-theory (e/d (fn-wscan-runp)
                                  (fn-wire-feed-byte fn-wscan-ordinaryp fn-wire-take-octet
                                   fn-wscan-plain-end fn-oct-get-is-nth)))))))

(local
 (defthm fn-wscan-span-fold-closed
   (implies (and (equal (fn-wire-state-mode ws) :closed)
                 (natp i) (natp end) (<= i end))
            (equal (fn-wire-span-fold ws i end fn-octets)
                   (fn-wsp-make ws nil end)))
   :hints (("Goal" :induct (fn-wire-span-fold ws i end fn-octets)
            :in-theory (enable fn-wire-feed-byte)))))

;; The whole-line branch.  The line built forward is the reverse of the one
;; consed onto an empty line-rev (fn-wscan-reverse-revonto), fn-wire-after-line
;; reads only the mode, the body and the limits (fn-wscan-after-line-after-run),
;; and CR LF after the run is the reference's two steps (fn-wscan-span-fold-crlf).
(local
 (defthm fn-wscan-slice-onto-empty
   (equal (fn-wscan-slice-onto i i acc fn-octets) acc)
   :hints (("Goal" :expand ((fn-wscan-slice-onto i i acc fn-octets))))))

(local
 (defthm fn-wscan-slice-onto-split
   (implies (and (natp i) (natp j) (natp k) (<= i j) (<= j k))
            (equal (fn-wscan-slice-onto i k acc fn-octets)
                   (fn-wscan-slice-onto i j (fn-wscan-slice-onto j k acc fn-octets)
                                        fn-octets)))
   :hints (("Goal" :induct (fn-wscan-slice-onto j k acc fn-octets)))))

(local
 (defthm fn-wscan-slice-onto-first
   (implies (and (natp i) (natp k) (< i k))
            (equal (fn-wscan-slice-onto i k acc fn-octets)
                   (cons (fn-octets-get i fn-octets)
                         (fn-wscan-slice-onto (+ 1 i) k acc fn-octets))))
   :hints (("Goal" :use ((:instance fn-wscan-slice-onto-split (j (+ 1 i))))
            :in-theory (disable fn-wscan-slice-onto-split)))))

(local
 (defthm fn-wscan-reverse-revonto
   (equal (fn-wire-reverse-octets-aux (fn-wscan-revonto i k acc fn-octets) a)
          (fn-wire-reverse-octets-aux acc (fn-wscan-slice-onto i k a fn-octets)))
   :hints (("Goal" :induct (fn-wscan-revonto i k acc fn-octets)
            :in-theory (disable fn-wscan-slice-onto-split)))))

(local
 (defthm fn-wscan-after-line-after-run
   (implies (not (equal (fn-wire-state-mode ws) :article))
            (equal (fn-wire-after-line (fn-wscan-after-run ws i k fn-octets) line)
                   (fn-wire-after-line ws line)))
   :hints (("Goal" :in-theory (enable fn-wire-after-line fn-wscan-after-run
                                      fn-wire-close)))))

(local
 (defthm fn-wscan-span-fold-crlf
   (implies (and (fn-wire-state-shapep s)
                 (not (equal (fn-wire-state-mode s) :closed))
                 (not (fn-wire-state-pending-crp s))
                 (natp k) (natp end) (< (+ 1 k) end)
                 (equal (fn-octets-get k fn-octets) 13)
                 (equal (fn-octets-get (+ 1 k) fn-octets) 10))
            (equal (fn-wire-span-fold s k end fn-octets)
                   (let ((r (fn-wire-after-line
                             s (fn-wire-reverse-octets (fn-wire-state-line-rev s)))))
                     (if (consp (fn-wire-result-events r))
                         (fn-wsp-make (fn-wire-result-state r)
                                      (fn-wire-result-events r) (+ 2 k))
                       (fn-wire-span-fold (fn-wire-result-state r) (+ 2 k)
                                          end fn-octets)))))
   :hints (("Goal" :in-theory (e/d (fn-wire-feed-byte)
                                   (fn-wire-after-line fn-wire-reverse-octets))
            :expand ((fn-wire-span-fold s k end fn-octets)
                     (:free (x) (fn-wire-span-fold x (+ 1 k) end fn-octets)))))))

(local
 (defthm fn-wscan-span-fold-over-article-line
   (implies (and (fn-wscan-linep ws i end fn-octets)
                 (natp i) (natp end) (< i end)
                 (equal (fn-wire-state-mode ws) :article))
            (equal (fn-wire-span-fold ws i end fn-octets)
                   (let* ((k (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                                 (fn-wire-state-line-limit ws)
                                                 fn-octets))
                          (r (fn-wire-after-line (fn-wscan-after-run ws i k fn-octets) nil)))
                     (if (consp (fn-wire-result-events r))
                         (fn-wsp-make (fn-wire-result-state r)
                                      (fn-wire-result-events r) (+ 2 k))
                       (fn-wire-span-fold (fn-wire-result-state r) (+ 2 k)
                                          end fn-octets)))))
   :hints (("Goal"
            :use ((:instance fn-wscan-span-fold-over-run-any)
                  (:instance fn-wscan-linep-line-ends-inside (wire-state ws))
                  (:instance fn-wscan-span-fold-crlf
                             (s (fn-wscan-after-run
                                 ws i (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                                          (fn-wire-state-line-limit ws)
                                                          fn-octets)
                                 fn-octets))
                             (k (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                                    (fn-wire-state-line-limit ws)
                                                    fn-octets))))
            :in-theory (e/d (fn-wire-reverse-octets fn-wire-reverse-octets-aux)
                            (fn-wscan-span-fold-over-run-any
                             fn-wscan-span-fold-crlf
                             fn-wscan-linep-line-ends-inside
                             fn-wscan-ordinaryp
                             fn-wire-span-fold fn-wire-after-line
                             fn-wscan-plain-end)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (fn-wire-reverse-octets fn-wire-reverse-octets-aux
                                   fn-wscan-linep fn-wscan-runp fn-wscan-after-run)
                                  (fn-wscan-span-fold-over-run-any
                                   fn-wscan-span-fold-crlf
                                   fn-wscan-linep-line-ends-inside
                                   fn-wscan-ordinaryp
                                   fn-wire-span-fold fn-wire-after-line
                                   fn-wscan-plain-end fn-bchs-push-span)))))))

(local
(defthm fn-wscan-span-fold-over-command-line
   (implies (and (fn-wscan-linep ws i end fn-octets)
                 (natp i) (natp end) (< i end)
                 (not (equal (fn-wire-state-mode ws) :article)))
            (equal (fn-wire-span-fold ws i end fn-octets)
                   (let* ((k (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                                 (fn-wire-state-line-limit ws)
                                                 fn-octets))
                          (r (fn-wire-after-line
                              ws (fn-wscan-slice-onto i k nil fn-octets))))
                     (if (consp (fn-wire-result-events r))
                         (fn-wsp-make (fn-wire-result-state r)
                                      (fn-wire-result-events r) (+ 2 k))
                       (fn-wire-span-fold (fn-wire-result-state r) (+ 2 k)
                                          end fn-octets)))))
   :hints (("Goal"
            :use ((:instance fn-wscan-span-fold-over-run-any)
                  (:instance fn-wscan-linep-line-ends-inside (wire-state ws))
                  (:instance fn-wscan-span-fold-crlf
                             (s (fn-wscan-after-run
                                 ws i (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                                          (fn-wire-state-line-limit ws)
                                                          fn-octets)
                                 fn-octets))
                             (k (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                                    (fn-wire-state-line-limit ws)
                                                    fn-octets))))
            :in-theory (e/d (fn-wire-reverse-octets)
                            (fn-wscan-span-fold-over-run-any
                             fn-wscan-span-fold-crlf
                             fn-wscan-linep-line-ends-inside
                             fn-wscan-slice-onto-split fn-wscan-ordinaryp
                             fn-wire-span-fold fn-wire-after-line
                             fn-wscan-plain-end fn-wscan-slice-onto
                             fn-wscan-revonto)))
           (and stable-under-simplificationp
                '(:in-theory (e/d (fn-wire-reverse-octets fn-wscan-linep
                                   fn-wscan-runp fn-wscan-after-run)
                                  (fn-wscan-span-fold-over-run-any
                                   fn-wscan-span-fold-crlf
                                   fn-wscan-linep-line-ends-inside
                                   fn-wscan-slice-onto-split fn-wscan-ordinaryp
                                   fn-wire-span-fold fn-wire-after-line
                                   fn-wscan-plain-end fn-wscan-slice-onto
                                   fn-wscan-revonto)))))))

(local
 (defthm fn-wscan-span-fold-over-line
   (implies (and (fn-wscan-linep ws i end fn-octets)
                 (natp i) (natp end) (< i end))
            (equal (fn-wire-span-fold ws i end fn-octets)
                   (let* ((k (fn-wscan-plain-end i end (fn-wire-state-line-len ws)
                                                 (fn-wire-state-line-limit ws)
                                                 fn-octets))
                          (r (if (equal (fn-wire-state-mode ws) :article)
                                 (fn-wire-after-line (fn-wscan-after-run ws i k fn-octets) nil)
                               (fn-wire-after-line
                                ws (fn-wscan-slice-onto i k nil fn-octets)))))
                     (if (consp (fn-wire-result-events r))
                         (fn-wsp-make (fn-wire-result-state r)
                                      (fn-wire-result-events r) (+ 2 k))
                       (fn-wire-span-fold (fn-wire-result-state r) (+ 2 k)
                                          end fn-octets)))))
   :hints (("Goal" :use ((:instance fn-wscan-span-fold-over-article-line)
                         (:instance fn-wscan-span-fold-over-command-line))
                   :in-theory (disable fn-wscan-span-fold-over-article-line
                                       fn-wscan-span-fold-over-command-line
                                       fn-wire-span-fold fn-wire-after-line
                                       fn-wscan-plain-end fn-wscan-after-run
                                       fn-wscan-slice-onto)))))

; KEYSTONE (PKT-479), no hypothesis: the line-at-a-time scan the served fold
; runs is the octet-at-a-time fold, on every wire state and every range.
(defthm fn-wire-scan-is-span-fold
  (equal (fn-wire-scan wire-state i end fn-octets)
         (fn-wire-span-fold wire-state i end fn-octets))
  :hints (("Goal" :induct (fn-wire-scan wire-state i end fn-octets)
           :in-theory (e/d (fn-wire-scan)
                           (fn-wire-feed-byte fn-wscan-runp fn-wscan-linep
                            fn-wscan-ordinaryp fn-wscan-after-run
                            fn-wscan-plain-end fn-wire-after-line
                            fn-wscan-slice-onto fn-wscan-slice-onto-split)))
          (and stable-under-simplificationp
               '(:expand ((fn-wire-span-fold wire-state i end fn-octets))))))

(in-theory (disable fn-wire-scan))
