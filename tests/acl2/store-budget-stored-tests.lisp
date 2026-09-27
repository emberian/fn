; fn: witnesses and teeth for books/store-budget-stored.lisp (records-flip,
; flip-L1): the history budget counts a retained article row by the octets it
; stores, its payload's extent in the arena.
;
; The rows are reached by the open's intern (fn-intern-events) of wire
; records into a fresh local arena.  The corrupted-state witness (a held row
; whose facts disagree with its extent) is labelled as such.
(in-package "ACL2")
(include-book "../../books/store-budget-stored")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defconst *sbst-groups* '("fn.letters"))
(defconst *sbst-ws*
  (list (fn-record-make 0 0 0 "<a@example.invalid>" '(1 2 3) *sbst-groups*
                        "p" "s" "r" 2 841000000)
        (fn-record-make 1 1 0 "<b@example.invalid>" '(65 66 67 68 69) *sbst-groups*
                        "p" "s" "r" 2 841000000)))
(assert-event (fn-wire-event-listp *sbst-ws*))

; The open: the rows, the budget's octets, the stored octets over the arena,
; the relation, and the pre-flip count (the wire encoder over each row).
(defun sbst-old-count (rows)
  (declare (xargs :verify-guards nil))
  (if (consp rows)
      (+ (len (fn-store-event-encode (car rows))) (sbst-old-count (cdr rows)))
    0))

(defun sbst-open-in (ws generation fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events ws nil generation fn-arena)
    (mv (list (fn-sbud-record-octets rows)
              (fn-sbud-stored-octets rows fn-arena)
              (fn-sbud-rows-extents-okp rows fn-arena)
              (sbst-old-count rows)
              rows)
        fn-arena)))

(defun sbst-open (ws generation)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (sbst-open-in ws generation fn-arena)
      out)))

; REACHABLE (fn-intern-events-budget-octets-are-the-stored-octets,
; fn-intern-events-extents-okp): every hypothesis holds (the arena is the
; live one, generation 0, a wire event list); the relation holds; the budget
; counts 3 + 5 = 8 payload octets and each row's one membership at 320
; (lane membership-budget): 648, the stored charges, where the pre-flip count
; was 0.
(defconst *sbst-open* (sbst-open *sbst-ws* 0))
(assert-event (natp 0))
(assert-event (fn-held-listp (nth 4 *sbst-open*)))
(assert-event (equal (nth 2 *sbst-open*) t))
(assert-event (equal (nth 0 *sbst-open*) 648))
(assert-event (equal (nth 1 *sbst-open*) 648))
(assert-event (equal (nth 3 *sbst-open*) 0))

; The same through the store the host reads (fn-sbud-bytes-used over the
; kernel's records; fn-sbud-bytes-used-is-the-stored-octets).
(defconst *sbst-store*
  (list nil nil (fn-sf-make :ready 2 nil (nth 4 *sbst-open*) nil nil nil 0)))
(assert-event (equal (fn-sbud-bytes-used *sbst-store*) 648))
; The carried sum from a prefix cache agrees (fn-sbud-bytes-used-is-kernel-sum).
(assert-event (equal (fn-sbud-bytes-extend
                      (cons 1 (fn-sbud-record-octets (take 1 (nth 4 *sbst-open*))))
                      (nth 4 *sbst-open*))
                     648))
; A wire row still counts its encoding (fn-sbud-row-octets-of-wire-row).
(assert-event (equal (fn-sbud-row-octets (car *sbst-ws*))
                     (len (fn-store-event-encode (car *sbst-ws*)))))
(assert-event (< 0 (fn-sbud-row-octets (car *sbst-ws*))))

; CORRUPTED STATE (hypothesis removal for
; fn-sbud-record-octets-is-the-stored-octets, whose one hypothesis is the
; relation): the first row with its facts claiming 7 octets where its handle's
; extent is 3.  The relation fails, and so does the conclusion: the budget
; counts 7 + 5 + 640 = 652, the stored charges are 3 + 5 + 640 = 648.
(defconst *sbst-row0* (car (nth 4 *sbst-open*)))
(defconst *sbst-lying*
  (fn-held-make (fn-record-sequence *sbst-row0*) (fn-record-txid *sbst-row0*)
                (fn-record-generation *sbst-row0*) (fn-record-msgid *sbst-row0*)
                (fn-record-payload *sbst-row0*) (fn-record-groups *sbst-row0*)
                (fn-record-obligation-id *sbst-row0*)
                (fn-record-content-subject *sbst-row0*)
                (fn-record-release-evidence *sbst-row0*)
                (fn-record-charge *sbst-row0*) (fn-record-stamp *sbst-row0*)
                (fn-hf-make 7 (fn-hf-body-start (fn-held-facts *sbst-row0*))
                            (fn-hf-body-lines (fn-held-facts *sbst-row0*))
                            (fn-hf-control (fn-held-facts *sbst-row0*))
                            (fn-hf-nov (fn-held-facts *sbst-row0*)))
                (fn-held-context *sbst-row0*) nil nil))
(assert-event (fn-held-p *sbst-lying*))

(defun sbst-lying-in (ws fn-arena)
  (declare (xargs :stobjs fn-arena :verify-guards nil))
  (mv-let (rows fn-arena)
    (fn-intern-events ws nil 0 fn-arena)
    (let ((rows (cons *sbst-lying* (cdr rows))))
      (mv (list (fn-sbud-rows-extents-okp rows fn-arena)
                (fn-sbud-record-octets rows)
                (fn-sbud-stored-octets rows fn-arena))
          fn-arena))))

(defun sbst-lying (ws)
  (declare (xargs :verify-guards nil))
  (with-local-stobj fn-arena
    (mv-let (out fn-arena)
      (sbst-lying-in ws fn-arena)
      out)))

(defconst *sbst-lie* (sbst-lying *sbst-ws*))
(assert-event (equal (nth 0 *sbst-lie*) nil))
(assert-event (equal (nth 1 *sbst-lie*) 652))
(assert-event (equal (nth 2 *sbst-lie*) 648))
; The same refutation as a theorem over the arena's logical value (the two
; payloads the open sealed): the conclusion is false at these rows, so the
; theorem without its hypothesis fails.
(defconst *sbst-lying-rows* (cons *sbst-lying* (cdr (nth 4 *sbst-open*))))
(defconst *sbst-arena-value* '((1 2 3) (65 66 67 68 69)))
(thm (not (equal (fn-sbud-record-octets *sbst-lying-rows*)
                 (fn-sbud-stored-octets *sbst-lying-rows* *sbst-arena-value*))))
(thm (not (fn-sbud-rows-extents-okp *sbst-lying-rows* *sbst-arena-value*)))
(must-fail-checked
 (defthm sbst-octets-without-the-relation
   (equal (fn-sbud-record-octets *sbst-lying-rows*)
          (fn-sbud-stored-octets *sbst-lying-rows* *sbst-arena-value*))))

; The open keystone's other hypotheses: fn-arena-p and (natp generation) are
; fn-intern-events' guard (the host cannot call it outside them; a call at
; generation -1 is a guard violation), and fn-wire-event-listp is what the
; open's exact decoder hands it.  No removal witness is claimed for them.

; -----------------------------------------------------------------------------
; Lane membership-budget (2026-09-27).  fn-sbud-record-octets-pays-the-
; memberships (books/store-budget.lisp; no hypothesis): a reachable held row
; interned from a wire record crossposted to three groups is charged its
; payload and 3 x 320 = 960 octets, and holds 3 memberships; the history of
; it and the open's two rows pays 320 x 5 memberships out of 1,613 octets.
(defconst *sbst-cross-ws*
  (list (fn-record-make 2 2 0 "<c@example.invalid>" '(70 71 72 73)
                        '("fn.a" "fn.b" "fn.c") "p" "s" "r" 2 841000000)))
(assert-event (fn-wire-event-listp *sbst-cross-ws*))
(defconst *sbst-cross* (sbst-open *sbst-cross-ws* 0))
(defconst *sbst-cross-row* (car (nth 4 *sbst-cross*)))
(assert-event (fn-held-p *sbst-cross-row*))
(assert-event (equal (fn-sbud-row-memberships *sbst-cross-row*) 3))
(assert-event (equal (fn-sbud-row-octets *sbst-cross-row*) (+ 4 960)))
(assert-event (equal (nth 0 *sbst-cross*) 964))
(assert-event (equal (nth 1 *sbst-cross*) 964))
(assert-event (equal (nth 2 *sbst-cross*) t))
(defconst *sbst-all-rows* (append (nth 4 *sbst-open*) (nth 4 *sbst-cross*)))
(assert-event (equal (fn-sbud-record-memberships *sbst-all-rows*) 5))
(assert-event (equal (fn-sbud-record-octets *sbst-all-rows*) 1612))
(assert-event (<= (* *fn-sbud-membership-octets*
                     (fn-sbud-record-memberships *sbst-all-rows*))
                  (fn-sbud-record-octets *sbst-all-rows*)))
; A wire row (no groups of its own counted) holds no membership.
(assert-event (equal (fn-sbud-row-memberships (car *sbst-ws*)) 0))
; MUTATION (the charge before this lane): a row charged only its payload
; would not pay: 320 x 3 > 4.
(assert-event (not (<= (* *fn-sbud-membership-octets*
                          (fn-sbud-row-memberships *sbst-cross-row*))
                       (nfix (fn-hf-octets (fn-held-facts *sbst-cross-row*))))))

