; HDR :fn-enrollment (PKT-175, NNT-036): the CURRENT enrollment, in the
; node's keyring view pinned with the reader's archive, of the principal
; named by the historical verdict recorded for an article.
;
; Four facts stay separate (planning/handoff-2026-09-25-fable-mandate.md
; section 5.4): the historical signature verdict (HDR :fn-verified, the
; pinned verdict list, books/nntp-verdict.lisp), historical local acceptance,
; current enrollment (this book), and current administrative authority.  This
; item never changes or reinterprets the verdict: it reads the verdict only
; for the principal and generation it names, and reports that principal's
; newest snapshot in the pinned keyring view (`fn-hl-current-for-principal')
; with the state word `fn-hl-history-row' gives it.  The same disclosure
; class as HDR :fn-control: one line, Message-ID form only.
;
; The keyring view rides in the connection's control pin, a fourth slot
; (:keyring . SNAPSHOTS) beside the withdrawn list and the withdrawal
; records (`fn-enr-pin'; `fn-ctl-pin-withdrawn' and `fn-ctl-pin-ws' read
; the first two unchanged).  books/owner.lisp pins the Store's
; `fn-sn-keyring-snapshots' into each committed view at refresh
; (`fn-own-view-keyring'), so a reader never sees a later enrollment than
; its view's, exactly as it never sees a later verdict.
;
; Item grammar (specs/peering.md section 8; specs/human-client.md):
;   active HEX keyring N     the verdict's generation is the principal's
;                            current enrollment, generation N
;   retired HEX keyring N    the principal has enrolled generation N since;
;                            the verdict's generation is no longer current
;   revoked HEX keyring N    the principal's newest snapshot is the
;                            revocation tombstone at generation N
;   unenrolled HEX           the view holds no snapshot for the principal
;   none no-keyring-view     the connection pinned no keyring view
;   none no-record           no verdict is recorded for the article
;   none no-principal        the verdict names no 32-octet principal
; HEX is the verdict's principal in lowercase hex; N is decimal.
(in-package "ACL2")
(include-book "control-served")
(include-book "nntp-responses")
(include-book "stx-reader")
(include-book "hybrid-lifecycle")
(include-book "group-bucket-index")

;; The control pin with the keyring view.
(defun fn-enr-pin (withdrawn ws keyring)
  (declare (xargs :guard t))
  (list :fn-control withdrawn ws (cons :keyring keyring)))

(defun fn-enr-pin-slot (x)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr x)))))

(defun fn-enr-pin-has-keyring-p (x)
  (declare (xargs :guard t))
  (let ((slot (fn-enr-pin-slot x)))
    (and (consp slot) (eq (car slot) :keyring))))

(defun fn-enr-pin-keyring (x)
  (declare (xargs :guard t))
  (let ((slot (fn-enr-pin-slot x)))
    (if (and (consp slot) (eq (car slot) :keyring)) (cdr slot) nil)))

(defthm fn-enr-pin-fields
  (let ((p (fn-enr-pin withdrawn ws keyring)))
    (and p
         (equal (fn-ctl-pin-withdrawn p) withdrawn)
         (equal (fn-ctl-pin-ws p) ws)
         (fn-enr-pin-has-keyring-p p)
         (equal (fn-enr-pin-keyring p) keyring)))
  :hints (("Goal" :in-theory (enable fn-ag-car fn-ag-cdr))))

(defthm fn-enr-pin-of-nil-has-no-keyring
  (not (fn-enr-pin-has-keyring-p nil)))

(in-theory (disable fn-enr-pin fn-enr-pin-slot fn-enr-pin-has-keyring-p
                    fn-enr-pin-keyring))

;; The principal a verdict names: the 32-octet detail of a verified, revoked
;; or carried verdict (schema 1, books/stx-reader.lisp); nil otherwise.
(defun fn-enr-principal (verdict)
  (declare (xargs :guard t))
  (let ((token (fn-stx-verdict-token verdict))
        (detail (fn-stx-verdict-detail verdict)))
    (if (and (or (eq token :verified) (eq token :revoked) (eq token :carried))
             (fn-cbor-octet-listp detail)
             (equal (len detail) 32))
        detail
      nil)))

(defconst *fn-enr-active* '(97 99 116 105 118 101))              ; active
(defconst *fn-enr-retired* '(114 101 116 105 114 101 100))       ; retired
(defconst *fn-enr-revoked* '(114 101 118 111 107 101 100))       ; revoked
(defconst *fn-enr-unenrolled*
  '(117 110 101 110 114 111 108 108 101 100))                    ; unenrolled
(defconst *fn-enr-none-view*
  '(110 111 110 101 32 110 111 45 107 101 121 114 105 110 103 45 118 105 101
    119))                                                        ; none no-keyring-view
(defconst *fn-enr-none-record*
  '(110 111 110 101 32 110 111 45 114 101 99 111 114 100))       ; none no-record
(defconst *fn-enr-none-principal*
  '(110 111 110 101 32 110 111 45 112 114 105 110 99 105 112 97 108)) ; none no-principal

;; The state word of the principal's current row against the verdict's
;; generation.  `fn-hl-history-row' of the principal's own newest snapshot
;; is :revoked (a tombstone) or :active; an :active row at another
;; generation means the verdict's generation has been retired.
(defun fn-enr-word (row-state generation verdict-generation)
  (declare (xargs :guard t))
  (cond ((eq row-state :revoked) *fn-enr-revoked*)
        ((and (eq row-state :active) (equal generation verdict-generation))
         *fn-enr-active*)
        (t *fn-enr-retired*)))

(defun fn-enr-item (verdict control)
  (declare (xargs :guard t))
  (let ((principal (fn-enr-principal verdict)))
    (cond ((not (fn-enr-pin-has-keyring-p control)) *fn-enr-none-view*)
          ((not verdict) *fn-enr-none-record*)
          ((not principal) *fn-enr-none-principal*)
          (t
           (let* ((keyring (fn-enr-pin-keyring control))
                  (row (fn-hl-history-row
                        (fn-hl-current-for-principal principal keyring)
                        keyring)))
             (if (not row)
                 (append *fn-enr-unenrolled*
                         (cons 32 (fn-stx-hex-octets principal)))
               (append (fn-enr-word (cadr row) (car row)
                                    (fn-stx-verdict-generation verdict))
                       (cons 32
                             (append (fn-stx-hex-octets principal)
                                     (fn-stx-keyring-suffix (car row)))))))))))

(defthm fn-enr-item-is-printable
  (fn-stx-printablep (fn-enr-item verdict control))
  :hints (("Goal" :in-theory (e/d (fn-stx-printablep)
                                  (fn-stx-keyring-suffix fn-stx-hex-octets
                                   fn-hl-history-row
                                   fn-hl-current-for-principal)))))

;; The served arm.  The article is looked up in the pinned Message-ID trie of
;; the served list (one lookup), the verdict in the pinned verdict list.
(defun fn-nntp-enrollment-hdr-response (session archive index verdicts args)
  (declare (xargs :guard t)
           (ignorable archive))
  (if (and (consp args) (consp (cdr args)) (null (cddr args))
           (fn-nntp-message-id-tokenp (cadr args))
           (fn-octet-listp (cadr args)))
      (let ((msgid (fn-nntp-token-string (cadr args))))
        (if (not (consp (fn-midx-lookup msgid (fn-gidx-pin-trie index))))
            (fn-nntp-single session "430 no article with that message-id")
          (fn-nntp-multi
           session (fn-nntp-hdr-initial nil)
           (list (fn-nntp-hdr-line
                  (fn-nntp-decimal-field 0)
                  (fn-enr-item (fn-stx-reader-lookup msgid verdicts)
                               (fn-gidx-pin-control index)))))))
    (fn-nntp-single session "501 syntax error")))

(defthm fn-nntp-enrollment-hdr-response-preserves-session
  (equal (fn-nntp-result-session
          (fn-nntp-enrollment-hdr-response session archive index verdicts args))
         session)
  :hints (("Goal" :in-theory (e/d (fn-nntp-enrollment-hdr-response
                                   fn-nntp-single fn-nntp-multi
                                   fn-nntp-make-result fn-nntp-result-session)
                                  (fn-enr-item fn-nntp-hdr-line
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-midx-lookup fn-stx-reader-lookup
                                   fn-nntp-token-string fn-octet-listp)))))

(defthm fn-nntp-enrollment-hdr-response-effects-true-listp
  (true-listp (fn-nntp-result-effects
               (fn-nntp-enrollment-hdr-response session archive index verdicts args)))
  :hints (("Goal" :in-theory (e/d (fn-nntp-enrollment-hdr-response fn-nntp-single
                                   fn-nntp-multi fn-nntp-make-result
                                   fn-nntp-result-effects fn-nntp-reply-effect)
                                  (fn-enr-item
                                   fn-nntp-hdr-line fn-nntp-hdr-initial
                                   fn-nntp-stuff-lines fn-nntp-crlf
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-midx-lookup fn-stx-reader-lookup
                                   fn-nntp-token-string fn-octet-listp)))))

;; KEYSTONE (the arm): over a Message-ID the pinned trie holds, the reply is
;; one line, 0 and the enrollment item of the verdict recorded for that
;; Message-ID against the pin's keyring view.  (Stated here over the arm;
;; books/owner-enrollment-read.lisp states it over fn-own-read.)
(defthm fn-nntp-enrollment-hdr-response-is-the-pinned-enrollment
  (let ((msgid (fn-nntp-token-string (cadr args))))
    (implies (and (consp args) (consp (cdr args)) (null (cddr args))
                  (fn-nntp-message-id-tokenp (cadr args))
                  (fn-octet-listp (cadr args))
                  (consp (fn-midx-lookup msgid (fn-gidx-pin-trie index))))
             (equal (fn-nntp-enrollment-hdr-response session archive index
                                                     verdicts args)
                    (fn-nntp-multi
                     session (fn-nntp-hdr-initial nil)
                     (list (fn-nntp-hdr-line
                            (fn-nntp-decimal-field 0)
                            (fn-enr-item (fn-stx-reader-lookup msgid verdicts)
                                         (fn-gidx-pin-control index))))))))
  :hints (("Goal" :in-theory (e/d (fn-nntp-enrollment-hdr-response)
                                  (fn-enr-item fn-nntp-multi fn-nntp-hdr-line
                                   fn-nntp-decimal-field fn-nntp-message-id-tokenp
                                   fn-gidx-pin-control fn-gidx-pin-trie
                                   fn-midx-lookup fn-stx-reader-lookup
                                   fn-nntp-token-string fn-octet-listp)))))

;; What the item says, by case, over the pinned keyring view: the three
;; states are the principal's newest snapshot's row.
(defthm fn-enr-item-of-an-enrolled-principal
  (let* ((principal (fn-enr-principal verdict))
         (keyring (fn-enr-pin-keyring control))
         (row (fn-hl-history-row
               (fn-hl-current-for-principal principal keyring) keyring)))
    (implies (and (fn-enr-pin-has-keyring-p control)
                  verdict principal row)
             (equal (fn-enr-item verdict control)
                    (append (fn-enr-word (cadr row) (car row)
                                         (fn-stx-verdict-generation verdict))
                            (cons 32 (append (fn-stx-hex-octets principal)
                                             (fn-stx-keyring-suffix
                                              (car row))))))))
  :hints (("Goal" :in-theory (e/d () (fn-hl-history-row
                                      fn-hl-current-for-principal
                                      fn-stx-hex-octets fn-stx-keyring-suffix
                                      fn-enr-principal fn-enr-word)))))

(in-theory (disable fn-nntp-enrollment-hdr-response fn-enr-item))
