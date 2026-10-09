; Shared ARTICLE/HEAD/BODY producer. Payloads remain captured arena handles;
; preflight and rendering each consume a bounded number of octets per step,
; read a window at a time into a workspace and scanned by span instances
; (books/nntp-spans.lisp): the preflight folds `fn-nsp-frame-block', the
; payload is streamed by `fn-nsp-stuff'.  A READY cursor has no session or
; authorization effects.
(in-package "ACL2")
(include-book "nntp-responses")
(include-book "nov-piece-window")
(include-book "nntp-spans")
(include-book "assumptions-durable-spans")
(local (include-book "arithmetic-5/top" :dir :system))

; The workspace a quantum loads its payload window into (the owner's, cleared
; at each load; congruent to `fn-octets', so every span instance reads it).
(def-buffer fn-ast-ws :view t)

(defun fn-ast-at (i xs)
  (declare (xargs :guard (natp i) :measure (nfix i)))
  (if (consp xs)
      (if (zp i) (car xs) (fn-ast-at (- i 1) (cdr xs)))
    nil))

; Source = (handle offset remaining literal-tail). NIL handle denotes the
; logical/literal representation. Length is captured once with the handle.
(defun fn-ast-source (article fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((p (fn-article-payload article)))
    (if (and (natp p) (< p (fn-arena-count fn-arena)))
        (list p 0 (fn-arena-payload-len p fn-arena) nil)
      (let ((bytes (fn-nntp-article-bytes article fn-arena)))
        (list nil 0 (len bytes) bytes)))))
(fn-payload-kind fn-ast-source :handle "tests the payload as a natural below the arena count, reads its length there, and keeps the handle as the source's handle; the octets are read a window at a time by fn-ast-load")

(defun fn-ast-source-left (source left)
  (declare (xargs :guard (natp left)))
  (list (fn-ast-at 0 source) (nfix (fn-ast-at 1 source)) left (fn-ast-at 3 source)))

;; THE SPAN SOURCE.  A source's next N octets are a window: a handle's are
;; the arena's span from AT (fn-arena-get-span), a literal's the first N of
;; its tail.  `fn-ast-load' clears the workspace and reads the window into it,
;; a handle's through A-ARENA-SPAN-INTO (books/assumptions-durable-spans.lisp:
;; one host read into the buffer, no list); `fn-ast-source-avail' is how many
;; octets the source can still deliver.
(defun fn-ast-handlep (h fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (natp h) (< h (fn-arena-count fn-arena))))

(defun fn-ast-lit-take (n xs)
  (declare (xargs :guard (natp n)))
  (if (and (not (zp n)) (consp xs) (fn-cbor-octetp (car xs)))
      (cons (car xs) (fn-ast-lit-take (- n 1) (cdr xs)))
    nil))

(defthm fn-ast-lit-take-octets
  (fn-cbor-octet-listp (fn-ast-lit-take n xs))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp))))

(defthm fn-ast-lit-take-len
  (<= (len (fn-ast-lit-take n xs)) (nfix n))
  :rule-classes :linear)

(defun fn-ast-drop (n xs)
  (declare (xargs :guard (natp n)))
  (if (or (zp n) (atom xs)) xs (fn-ast-drop (- n 1) (cdr xs))))

(defun fn-ast-source-avail (source fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (let ((h (fn-ast-at 0 source)) (at (nfix (fn-ast-at 1 source)))
        (rem (nfix (fn-ast-at 2 source))))
    (cond ((fn-ast-handlep h fn-arena)
           (min rem (nfix (- (fn-arena-payload-len h fn-arena) at))))
          ((null h) (len (fn-ast-lit-take rem (fn-ast-at 3 source))))
          (t 0))))

; The executable probe: how many of the next WANT octets the source can
; deliver, in work bounded by WANT (a literal is walked no further than WANT).
(defun fn-ast-source-take (source want fn-arena)
  (declare (xargs :stobjs fn-arena :guard (natp want)))
  (let ((h (fn-ast-at 0 source)) (at (nfix (fn-ast-at 1 source)))
        (rem (nfix (fn-ast-at 2 source))))
    (cond ((fn-ast-handlep h fn-arena)
           (min (nfix want) (min rem (nfix (- (fn-arena-payload-len h fn-arena) at)))))
          ((null h) (len (fn-ast-lit-take (min (nfix want) rem) (fn-ast-at 3 source))))
          (t 0))))

(local
 (defun fn-ast-lit-ind2 (a b xs)
   (if (or (zp a) (zp b) (atom xs)) (list a b xs)
     (fn-ast-lit-ind2 (- a 1) (- b 1) (cdr xs)))))

(local
 (defthm fn-ast-lit-take-len-min
   (implies (and (natp a) (natp b))
            (equal (len (fn-ast-lit-take (min a b) xs))
                   (min a (len (fn-ast-lit-take b xs)))))
   :hints (("Goal" :induct (fn-ast-lit-ind2 a b xs)))))

(defthm fn-ast-source-take-is-min
  (equal (fn-ast-source-take source want fn-arena)
         (min (nfix want) (fn-ast-source-avail source fn-arena)))
  :hints (("Goal" :in-theory (disable fn-ast-lit-take fn-ast-lit-take-len-min)
                  :use ((:instance fn-ast-lit-take-len-min (a (nfix want)) (b (nfix (fn-ast-at 2 source)))
                                   (xs (fn-ast-at 3 source)))))))

(defun fn-ast-source-window (source n fn-arena)
  (declare (xargs :stobjs fn-arena
                  :guard (and (natp n) (<= n (fn-ast-source-avail source fn-arena)))
                  :guard-hints (("Goal" :in-theory (disable fn-ast-at fn-ast-lit-take)))))
  (let ((h (fn-ast-at 0 source)) (at (nfix (fn-ast-at 1 source))))
    (cond ((not (fn-ast-handlep h fn-arena)) (fn-ast-lit-take n (fn-ast-at 3 source)))
          ((<= (+ at (nfix n)) (fn-arena-payload-len h fn-arena)) (fn-arena-get-span h at (nfix n) fn-arena))
          (t nil))))

(defun fn-ast-source-advance (source n)
  (declare (xargs :guard (natp n)))
  (list (fn-ast-at 0 source) (+ (nfix n) (nfix (fn-ast-at 1 source)))
        (nfix (- (nfix (fn-ast-at 2 source)) (nfix n))) (fn-ast-drop n (fn-ast-at 3 source))))

(defun fn-ast-load (source n fn-arena fn-ast-ws)
  (declare (xargs :stobjs (fn-arena fn-ast-ws)
                  :guard (and (natp n) (<= n (fn-ast-source-avail source fn-arena)))
                  :guard-hints (("Goal" :in-theory (disable fn-ast-at fn-ast-lit-take)))))
  (let* ((h (fn-ast-at 0 source)) (at (nfix (fn-ast-at 1 source)))
         (fn-ast-ws (fn-ast-ws-clear fn-ast-ws)))
    (cond ((not (fn-ast-handlep h fn-arena))
           (fn-ast-ws-append-list (fn-ast-lit-take n (fn-ast-at 3 source)) fn-ast-ws))
          ((<= (+ at n) (fn-arena-payload-len h fn-arena)) (fn-arena-get-span-into h at n fn-arena fn-ast-ws))
          (t fn-ast-ws))))

;; The window a load leaves in the workspace (A-ARENA-SPAN-INTO for a handle).
(defthm fn-ast-load-is-window
  (implies (and (natp n) (<= n (fn-ast-source-avail source fn-arena)))
           (equal (fn-ast-load source n fn-arena fn-ast-ws)
                  (fn-ast-source-window source n fn-arena)))
  :hints (("Goal" :in-theory (enable fn-arena-get-span-into-is-append-list fn-ast-ws-append-list
                                     fn-octets$a-append-list))))

(local
 (defun fn-ast-span-ind (at n)
   (if (zp n) at (fn-ast-span-ind (+ 1 at) (1- n)))))

(defthm fn-ast-span-len
  (equal (len (fn-arena-get-span h at n fn-arena)) (nfix n))
  :hints (("Goal" :induct (fn-ast-span-ind at n)
                  :in-theory (enable fn-arena-get-span-is-the-gets))))

(local
 (defun fn-ast-lit-ind (n k xs)
   (if (or (zp n) (zp k) (atom xs)) (list n k xs)
     (fn-ast-lit-ind (- n 1) (- k 1) (cdr xs)))))

(local
 (defthm fn-ast-lit-take-len-prefix
   (implies (and (natp n) (<= n (len (fn-ast-lit-take k xs))))
            (equal (len (fn-ast-lit-take n xs)) n))
   :hints (("Goal" :induct (fn-ast-lit-ind n k xs)))))

(defthm fn-ast-source-window-len
  (implies (and (natp n) (<= n (fn-ast-source-avail source fn-arena)))
           (equal (len (fn-ast-source-window source n fn-arena)) n))
  :hints (("Goal" :in-theory (enable fn-arena-get-span-is-the-gets))))

(defthm fn-ast-load-len
  (implies (and (natp n) (<= n (fn-ast-source-avail source fn-arena)))
           (equal (len (fn-ast-load source n fn-arena fn-ast-ws)) n))
  :hints (("Goal" :in-theory (disable fn-ast-load fn-ast-source-window fn-ast-source-avail))))

(defthm fn-ast-source-window-octets
  (implies (and (fn-arena-p fn-arena) (natp n) (<= n (fn-ast-source-avail source fn-arena)))
           (fn-cbor-octet-listp (fn-ast-source-window source n fn-arena)))
  :hints (("Goal" :in-theory (disable fn-ast-at fn-ast-lit-take))))

(defthm fn-ast-load-octets
  (implies (and (fn-arena-p fn-arena) (natp n) (<= n (fn-ast-source-avail source fn-arena)))
           (fn-cbor-octet-listp (fn-ast-load source n fn-arena fn-ast-ws)))
  :hints (("Goal" :in-theory (disable fn-ast-load fn-ast-source-window fn-ast-source-avail))))

;; Preflight = (:span source original acc he body): SOURCE what is left to scan,
;; ORIGINAL the payload's source, ACC the framing fold `fn-nsp-frame-block'
;; (books/nntp-spans.lisp) over the octets scanned so far, HE the header
;; block's end (its last CRLF included) from the payload's start once the
;; CRLF CRLF is found, BODY the source from the body's first octet, taken in
;; the quantum that finds it (a skip within that quantum, never a second walk
;; over the header).  Each quantum folds its window from ACC's flags with
;; the fold's count at zero (until the find), so the count never exceeds one
;; window and the head end is exact for a payload of any length; no constant
;; bounds the article (D27).  A refused preflight is done with the BAD bit set.
(defconst *fn-ast-acc-bad* 4)

; No quantum reads or writes more than 2^40 octets (every index stays a fixnum).
(defconst *fn-ast-window-max* (expt 2 40))

(defun fn-ast-preflight (source)
  (declare (xargs :guard t))
  (list :span source source *fn-nsp-block-init* nil nil))

(defun fn-ast-refused-preflight (source)
  (declare (xargs :guard t))
  (list :span (fn-ast-source-left source 0) source *fn-ast-acc-bad* nil nil))

(defun fn-ast-acc-foundp (acc)
  (declare (xargs :guard (natp acc)))
  (eql (mod (floor acc 8) 8) 4))

(defun fn-ast-scan-acc (scan)
  (declare (xargs :guard t))
  (let ((acc (fn-ast-at 3 scan)))
    (if (unsigned-byte-p 59 acc) acc *fn-ast-acc-bad*)))

; Numeric/current selection retains the archive spine and compares one group
; character per transition. The first membership for a group decides its
; number, exactly as fn-nntp-membership-number; later duplicates never win.
(defun fn-ast-select-state (mode group number remaining article members row at phase)
  (declare (xargs :guard t))
  (list :article-select mode group number remaining article members row at phase))

(defun fn-ast-select-donep (it)
  (declare (xargs :guard t))
  (member-eq (fn-ast-at 9 it) '(:selected :missing)))

; Message-ID uses the same retained selector. While finding a non-indexed
; article NUMBER carries the requested ID; after finding it, membership steps
; settle the optional selected-group number. Neither phase changes the reader.
(defun fn-ast-msgid-local-start (group article)
  (declare (xargs :guard t))
  (fn-ast-select-state :msgid group 0 nil article
                       (fn-article-memberships article) nil 0
                       (if (consp article) :members :missing)))

(defun fn-ast-msgid-local-done (it raw-number)
  (declare (xargs :guard t))
  (let ((article (fn-ast-at 5 it)))
    (fn-ast-select-state :msgid (fn-ast-at 2 it)
      (if (and (posp raw-number) (<= raw-number *fn-nntp-max-article-number*)
               (fn-nntp-article-idp article)) raw-number 0)
      nil article nil nil 0 :selected)))

(defun fn-ast-msgid-search-one (it)
  (declare (xargs :guard t))
  (let* ((mode (fn-ast-at 1 it)) (group (fn-ast-at 2 it)) (key (fn-ast-at 3 it))
         (remaining (fn-ast-at 4 it)) (article (fn-ast-at 5 it))
         (stored (fn-article-msgid article)) (at (nfix (fn-ast-at 8 it)))
         (next (fn-ast-select-state mode group key (fn-cbor-ag-cdr remaining)
                                    nil nil nil 0 :msgid-next)))
    (cond
     ((not (stringp key))
      (fn-ast-select-state mode group key nil nil nil nil 0 :missing))
     ((eq (fn-ast-at 9 it) :msgid-next)
      (if (consp remaining)
          (fn-ast-select-state mode group key remaining (car remaining)
                               nil nil 0 :msgid-compare)
        (fn-ast-select-state mode group key nil nil nil nil 0 :missing)))
     ((not (and (stringp stored) (equal (length key) (length stored)))) next)
     ((>= at (length key))
      (if (eq mode :withdrawn-msgid)
          (fn-ast-select-state mode group key remaining article nil nil 0 :selected)
        (fn-ast-msgid-local-start group article)))
     ((equal (char key at) (char stored at))
      (fn-ast-select-state mode group key remaining article nil nil (+ 1 at) :msgid-compare))
     (t next))))

(defun fn-ast-select-one (it)
  (declare (xargs :guard t))
  (let* ((mode (fn-ast-at 1 it)) (group (fn-ast-at 2 it)) (number (fn-ast-at 3 it))
         (remaining (fn-ast-at 4 it)) (article (fn-ast-at 5 it))
         (members (fn-ast-at 6 it)) (row (fn-ast-at 7 it))
         (row-group (fn-cbor-ag-car row))
         (at (nfix (fn-ast-at 8 it))) (phase (fn-ast-at 9 it))
         (next (fn-ast-select-state mode group number (fn-cbor-ag-cdr remaining)
                                    nil nil nil 0 :next)))
    (cond
     ((fn-ast-select-donep it) it)
     ((and (member-eq mode '(:msgid :withdrawn-msgid))
           (member-eq phase '(:msgid-next :msgid-compare)))
      (fn-ast-msgid-search-one it))
     ((not (stringp group))
      (if (eq mode :msgid) (fn-ast-msgid-local-done it 0)
        (fn-ast-select-state mode group number nil nil nil nil 0 :missing)))
     ((eq phase :next)
      (if (atom remaining)
          (fn-ast-select-state mode group number nil nil nil nil 0 :missing)
        (fn-ast-select-state mode group number remaining (car remaining)
                             (fn-article-memberships (car remaining)) nil 0 :members)))
     ((eq phase :members)
      (if (atom members) (if (eq mode :msgid) (fn-ast-msgid-local-done it 0) next)
        (let ((candidate (car members)))
          (if (and (consp candidate) (stringp (car candidate))
                   (equal (length group) (length (car candidate))))
              (fn-ast-select-state mode group number remaining article members candidate 0 :compare)
            (fn-ast-select-state mode group number remaining article (cdr members) nil 0 :members)))))
     ((not (and (eq phase :compare) (consp row) (stringp row-group)
                (equal (length row-group) (length group)))) next)
     (t
      (if (>= at (length group))
          (if (eq mode :msgid) (fn-ast-msgid-local-done it (cdr row))
           (if (and (equal number (cdr row))
                   (or (not (eq mode :current)) (fn-nntp-article-idp article)))
              (fn-ast-select-state mode group number remaining article members row at :selected)
            next))
        (if (equal (char group at) (char row-group at))
            (fn-ast-select-state mode group number remaining article members row (+ 1 at) :compare)
          (fn-ast-select-state mode group number remaining article
                               (fn-cbor-ag-cdr members) nil 0 :members)))))))

(defun fn-ast-select-step (it fuel)
  (declare (xargs :guard (natp fuel) :measure (nfix fuel)))
  (if (or (zp fuel) (fn-ast-select-donep it)) it
    (fn-ast-select-step (fn-ast-select-one it) (- fuel 1))))

; Arbitrary splitting of a work quantum preserves the exact retained cursor,
; including terminal replies. This says nothing about an archive reference.
(defthm fn-ast-select-fuel-composes
  (equal (fn-ast-select-step (fn-ast-select-step it a) b)
         (fn-ast-select-step it (+ (nfix a) (nfix b))))
  :rule-classes nil
  :hints (("Goal" :induct (fn-ast-select-step it a)
                  :in-theory (disable fn-ast-select-one fn-ast-select-donep))))

;; The header end and the body's source after a quantum: kept once found,
;; taken from the window in the quantum whose fold finds the CRLF CRLF.
(defun fn-ast-found (foundp scan source base m acc2)
  (declare (xargs :guard (and (natp base) (natp m) (natp acc2))))
  (cond (foundp (mv (fn-ast-at 4 scan) (fn-ast-at 5 scan)))
        ((fn-ast-acc-foundp acc2)
         (mv (nfix (- (+ base (floor acc2 64)) 2))
             (fn-ast-source-advance source (min m (floor acc2 64)))))
        (t (mv nil nil))))

;; One preflight quantum: up to FUEL octets of the source loaded into the
;; workspace and folded by `fn-nsp-frame-block' into ACC.  A source that
;; claims octets it cannot deliver (a payload shorter than its length, or a
;; literal with a non-octet) ends the scan with the BAD bit set.
(defun fn-ast-scan-step (scan fuel fn-arena fn-ast-ws)
  (declare (xargs :stobjs (fn-arena fn-ast-ws) :guard (natp fuel)
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-ast-load fn-ast-source-avail fn-ast-at
                                                     fn-ast-source-take fn-nsp-frame-block
                                                     fn-ast-load-is-window fn-ast-found)))))
  (let* ((source (fn-ast-at 1 scan)) (original (fn-ast-at 2 scan))
         (acc (fn-ast-scan-acc scan)) (rem (nfix (fn-ast-at 2 source))))
    (cond ((or (zp rem) (zp fuel)) (mv scan fn-ast-ws))
          (t (let ((n (fn-ast-source-take source (min (nfix fuel) *fn-ast-window-max*) fn-arena)))
               (if (zp n)
                   (mv (list :span (fn-ast-source-left source 0) original *fn-ast-acc-bad* nil nil) fn-ast-ws)
                 (let* ((fn-ast-ws (fn-ast-load source n fn-arena fn-ast-ws))
                        (m (min n (fn-ast-ws-len fn-ast-ws)))
                        (foundp (fn-ast-acc-foundp acc))
                        (acc2 (fn-nsp-frame-block (if foundp acc (mod acc 64)) 0 m fn-ast-ws))
                        (base (nfix (- (nfix (fn-ast-at 1 source)) (nfix (fn-ast-at 1 original))))))
                   (mv-let (he body) (fn-ast-found foundp scan source base m acc2)
                     (mv (list :span (fn-ast-source-advance source m) original acc2 he body)
                         fn-ast-ws)))))))))

(defun fn-ast-scan-donep (scan)
  (declare (xargs :guard t))
  (zp (nfix (fn-ast-at 2 (fn-ast-at 1 scan)))))

;; Valid: scanned to the end and framed (every line CRLF, no NUL, bare CR or
;; bare LF, the header block ended by CRLF CRLF).
(defun fn-ast-scan-validp (scan)
  (declare (xargs :guard t))
  (and (fn-ast-scan-donep scan)
       (fn-nsp-block-framedp (fn-ast-scan-acc scan))))

; No decimal field is expanded wholesale: the existing proved numerical
; piece setup divides once per work unit, then emits one digit per unit.
(defun fn-ast-initial-pieces (kind number article)
  (declare (xargs :guard t))
  (list (cond ((eq kind :article) "220 ") ((eq kind :head) "221 ")
              ((eq kind :body) "222 ") (t "223 "))
        (list :decimal (nfix number) nil) " "
        (if (stringp (fn-article-msgid article)) (fn-article-msgid article) "")
        (cond ((eq kind :article) " article follows")
              ((eq kind :head) " headers follow")
              ((eq kind :body) " body follows") (t " retrieved")) '(13 10)))

; Cursor = (phase pieces position pairs source line-start). Synthetic Xref
; locations are opened one pair at a time; the original pair list persists
; across replay. The caller passes pairs from the captured selected article.
(defun fn-ast-ready (scan kind number article server pairs)
  (declare (xargs :guard t))
  (let* ((original (fn-ast-at 2 scan))
         (he (nfix (fn-ast-at 4 scan)))
         (source (cond ((eq kind :body) (fn-ast-at 5 scan))
                       ((eq kind :head) (fn-ast-source-left original he))
                       (t original))))
    (list :initial (fn-ast-initial-pieces kind number article) 0
          (and (not (eq kind :body)) pairs) source t server)))

; Xref filtering retains the original membership spine. Word validation and
; the reference's first matching group lookup each advance one character or
; one membership per transition, including duplicate/corrupted memberships.
; Iterator = (:xref-source remaining all phase pair position lookup compare).
(defun fn-ast-xref-state (remaining all phase pair at lookup compare)
  (declare (xargs :guard t))
  (list :xref-source remaining all phase pair at lookup compare))

(defun fn-ast-xref-one (it)
  (declare (xargs :guard t))
  (let* ((remaining (fn-ast-at 1 it)) (all (fn-ast-at 2 it))
         (phase (fn-ast-at 3 it)) (pair (fn-ast-at 4 it))
         (at (nfix (fn-ast-at 5 it))) (lookup (fn-ast-at 6 it))
         (compare (nfix (fn-ast-at 7 it)))
         (skip (fn-ast-xref-state (fn-cbor-ag-cdr remaining) all :next nil 0 nil 0)))
    (cond
     ((eq phase :next)
      (if (atom remaining) (mv :end nil it)
        (let ((candidate (car remaining)))
          (if (and (consp candidate) (stringp (car candidate))
                   (< 0 (length (car candidate)))
                   (integerp (cdr candidate)) (< 0 (cdr candidate))
                   (<= (cdr candidate) *fn-nntp-max-article-number*))
            (mv :wait nil (fn-ast-xref-state remaining all :word candidate 0 nil 0))
            (mv :wait nil skip)))))
     ((not (and (consp pair) (stringp (car pair)) (< 0 (length (car pair)))
                (integerp (cdr pair)) (< 0 (cdr pair))
                (<= (cdr pair) *fn-nntp-max-article-number*)))
      (mv :wait nil skip))
     ((eq phase :word)
      (if (>= at (length (car pair)))
          (mv :wait nil (fn-ast-xref-state remaining all :lookup pair 0 all 0))
        (if (let ((byte (char-code (char (car pair) at))))
              (and (<= 33 byte) (<= byte 126) (not (equal byte 58))))
            (mv :wait nil (fn-ast-xref-state remaining all :word pair (+ 1 at) nil 0))
          (mv :wait nil skip))))
     ((eq phase :lookup)
      (if (atom lookup) (mv :wait nil skip)
        (let ((row (car lookup)))
          (if (and (consp row) (stringp (car row))
                   (equal (length (car row)) (length (car pair))))
              (mv :wait nil (fn-ast-xref-state remaining all :compare pair 0 lookup 0))
            (mv :wait nil (fn-ast-xref-state remaining all :lookup pair 0 (cdr lookup) 0))))))
     ((not (and (eq phase :compare) (consp lookup) (consp (car lookup))
                (stringp (car (car lookup)))
                (equal (length (car pair)) (length (car (car lookup))))))
      (mv :wait nil skip))
     (t
      (if (>= compare (length (car pair)))
          (mv (if (equal (cdr (car lookup)) (cdr pair)) :pair :wait) pair skip)
        (if (equal (char (car pair) compare) (char (car (car lookup)) compare))
            (mv :wait nil (fn-ast-xref-state remaining all :compare pair 0 lookup (+ 1 compare)))
          (mv :wait nil (fn-ast-xref-state remaining all :lookup pair 0 (cdr lookup) 0))))))))

(defthm fn-ast-xref-one-pair-is-numbered
  (implies (eq (mv-nth 0 (fn-ast-xref-one it)) :pair)
           (let ((pair (mv-nth 1 (fn-ast-xref-one it))))
             (and (consp pair) (stringp (car pair)) (< 0 (length (car pair)))
                  (integerp (cdr pair)) (< 0 (cdr pair))
                  (<= (cdr pair) *fn-nntp-max-article-number*))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-ast-xref-one) (fn-ast-at fn-ast-xref-state)))))

; Server validity is checked before any Xref bytes are published. Retain the
; original octet spine and consume one octet per transition; malformed/improper
; server lists omit Xref exactly as fn-nntp-xref-server does.
(defun fn-ast-server-state (original remaining)
  (declare (xargs :guard t))
  (list :xref-server original remaining))

(defun fn-ast-server-one (server-state)
  (declare (xargs :guard t))
  (let ((remaining (fn-ast-at 2 server-state)))
    (if (consp remaining)
        (if (and (integerp (car remaining))
                 (<= 33 (car remaining)) (<= (car remaining) 126))
            (mv :wait (fn-ast-server-state (fn-ast-at 1 server-state) (cdr remaining)))
          (mv :invalid server-state))
      (mv (if (null remaining) :valid :invalid) server-state))))

(defun fn-ast-ready-memberships (scan kind number article server)
  (declare (xargs :guard t))
  (let ((cur (fn-ast-ready scan kind number article server nil)))
    (list (fn-ast-at 0 cur) (fn-ast-at 1 cur) (fn-ast-at 2 cur)
          (and (consp server) (not (eq kind :body)) (fn-nntp-article-idp article)
               (fn-ast-xref-state (fn-article-memberships article)
                                  (fn-article-memberships article) :next nil 0 nil 0))
          (fn-ast-at 4 cur) (fn-ast-at 5 cur)
          (fn-ast-server-state server server))))

;; What a cursor may hold. FN-AST-CURSORP is the guard of the render transition: the
; piece list is what fn-npw-one consumes, and the phase's other fields are what
; the phase reads when it builds the next piece list. A cursor is created by
; fn-ast-ready-memberships (its server state is (:xref-server S S)) and every
; transition below keeps the invariant (fn-ast-render-one-keeps-cursorp).
; SRV-TAILP: REM is a tail of ORIG and every octet of ORIG before it is a valid
; server octet; with REM = NIL that makes ORIG an octet list.
(defun fn-ast-srv-tailp (orig rem)
  (declare (xargs :guard t))
  (or (equal orig rem)
      (and (consp orig) (integerp (car orig))
           (<= 33 (car orig)) (<= (car orig) 126)
           (fn-ast-srv-tailp (cdr orig) rem))))

(defun fn-ast-server-statep (s)
  (declare (xargs :guard t))
  (fn-ast-srv-tailp (fn-ast-at 1 s) (fn-ast-at 2 s)))

(defun fn-ast-xref-pairsp (pairs)
  (declare (xargs :guard t))
  (if (consp pairs)
      (and (consp (car pairs)) (stringp (car (car pairs)))
           (fn-ast-xref-pairsp (cdr pairs)))
    (null pairs)))

(defun fn-ast-cursorp (cur fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (fn-npw-piecesp (fn-ast-at 1 cur) fn-arena)
       (let ((phase (fn-ast-at 0 cur)))
         (cond
          ((eq phase :initial)
           (or (null (fn-ast-at 3 cur))
               (and (consp (fn-ast-at 3 cur)) (eq (car (fn-ast-at 3 cur)) :xref-source)
                    (fn-ast-server-statep (fn-ast-at 6 cur)))
               (and (fn-ast-xref-pairsp (fn-ast-at 3 cur))
                    (fn-cbor-octet-listp (fn-ast-at 6 cur)))))
          ((eq phase :xref-server) (fn-ast-server-statep (fn-ast-at 6 cur)))
          ((eq phase :xref-seek-first) (fn-cbor-octet-listp (fn-ast-at 6 cur)))
          ((eq phase :xref) (fn-ast-xref-pairsp (fn-ast-at 3 cur)))
          (t t)))))

; Each transition spends one unit, even when numerical setup or a phase
; transition produces no bytes.  The payload phase is not a transition: the
; window renders it a quantum at a time (fn-ast-render-window-aux below).
(defun fn-ast-render-one (cur fn-arena)
  (declare (xargs :stobjs fn-arena :guard (fn-ast-cursorp cur fn-arena)
                  :guard-hints (("Goal" :in-theory (disable fn-npw-one fn-npw-piecesp)))))
  (let ((phase (fn-ast-at 0 cur)) (pieces (fn-ast-at 1 cur)) (pos (nfix (fn-ast-at 2 cur))))
    (cond
     ((eq phase :done) (mv nil cur))
     ((consp pieces)
      (mv-let (out next at) (fn-npw-one pieces pos fn-arena)
        (mv out (list phase next at (fn-ast-at 3 cur) (fn-ast-at 4 cur) (fn-ast-at 5 cur) (fn-ast-at 6 cur)))))
     ((eq phase :initial)
      (if (eq (fn-ast-at 0 (fn-ast-at 3 cur)) :xref-source)
          (mv nil (list :xref-server nil 0 (fn-ast-at 3 cur) (fn-ast-at 4 cur) t (fn-ast-at 6 cur)))
       (if (consp (fn-ast-at 3 cur))
          (mv nil (list :xref (list "Xref: " (fn-ast-at 6 cur)) 0
                        (fn-ast-at 3 cur) (fn-ast-at 4 cur) t nil))
        (mv nil (list :payload nil 0 nil (fn-ast-at 4 cur) t nil)))))
     ((eq phase :xref-server)
      (mv-let (word next) (fn-ast-server-one (fn-ast-at 6 cur))
        (cond
         ((eq word :valid)
          (mv nil (list :xref-seek-first nil 0 (fn-ast-at 3 cur)
                        (fn-ast-at 4 cur) t (fn-ast-at 1 next))))
         ((eq word :invalid)
          (mv nil (list :payload nil 0 nil (fn-ast-at 4 cur) t nil)))
         (t (mv nil (list :xref-server nil 0 (fn-ast-at 3 cur)
                          (fn-ast-at 4 cur) t next))))))
     ((member-eq phase '(:xref-seek-first :xref-seek))
      (mv-let (word pair next) (fn-ast-xref-one (fn-ast-at 3 cur))
        (cond
         ((eq word :pair)
          (mv nil (list :xref-seek
                    (append (and (eq phase :xref-seek-first) (list "Xref: " (fn-ast-at 6 cur)))
                            (list " " (car pair) ":" (list :decimal (nfix (cdr pair)) nil)))
                    0 next (fn-ast-at 4 cur) t nil)))
         ((eq word :end)
          (mv nil (list :payload (and (eq phase :xref-seek) (list '(13 10)))
                        0 nil (fn-ast-at 4 cur) t nil)))
         (t (mv nil (list phase nil 0 next (fn-ast-at 4 cur) t (fn-ast-at 6 cur)))))))
     ((eq phase :xref)
      (if (consp (fn-ast-at 3 cur))
          (let ((pair (car (fn-ast-at 3 cur))))
            (mv nil (list :xref
                          (list " " (car pair) ":" (list :decimal (nfix (cdr pair)) nil))
                          0 (cdr (fn-ast-at 3 cur)) (fn-ast-at 4 cur) t nil)))
        (mv nil (list :payload (list '(13 10)) 0 nil (fn-ast-at 4 cur) t nil))))
     ((eq phase :payload) (mv nil cur))
     (t (mv nil (list :done nil 0 nil nil nil nil))))))

(local
 (progn
   (defthm fn-ast-srv-tailp-step
     (implies (and (fn-ast-srv-tailp orig rem) (consp rem)
                   (integerp (car rem)) (<= 33 (car rem)) (<= (car rem) 126))
              (fn-ast-srv-tailp orig (cdr rem)))
     :hints (("Goal" :in-theory (enable fn-ast-srv-tailp))))
   (defthm fn-ast-srv-tailp-nil-octets
     (implies (fn-ast-srv-tailp orig nil) (fn-cbor-octet-listp orig))
     :hints (("Goal" :in-theory (enable fn-ast-srv-tailp))))
   (defthm fn-ast-server-one-keeps-statep
     (implies (fn-ast-server-statep s)
              (fn-ast-server-statep (mv-nth 1 (fn-ast-server-one s))))
     :hints (("Goal" :in-theory (enable fn-ast-server-one fn-ast-server-statep
                                        fn-ast-server-state fn-ast-at))))
   (defthm fn-ast-server-one-valid-octets
     (implies (and (fn-ast-server-statep s)
                   (eq (mv-nth 0 (fn-ast-server-one s)) :valid))
              (fn-cbor-octet-listp (fn-ast-at 1 (mv-nth 1 (fn-ast-server-one s)))))
     :hints (("Goal" :in-theory (enable fn-ast-server-one fn-ast-server-statep fn-ast-at))))
   (defthm fn-ast-xref-pairsp-not-source
     (implies (and (fn-ast-xref-pairsp x) (consp x))
              (not (equal (car x) :xref-source)))
     :hints (("Goal" :in-theory (enable fn-ast-xref-pairsp))))
   (defthm fn-ast-xref-pairsp-cdr
     (implies (and (fn-ast-xref-pairsp x) (consp x))
              (fn-ast-xref-pairsp (cdr x)))
     :hints (("Goal" :in-theory (enable fn-ast-xref-pairsp))))
   (defthm fn-ast-xref-pairsp-car
     (implies (and (fn-ast-xref-pairsp x) (consp x))
              (and (consp (car x)) (stringp (car (car x)))))
     :hints (("Goal" :in-theory (enable fn-ast-xref-pairsp))))
   (defthm fn-ast-xref-one-pair-stringp
     (implies (eq (mv-nth 0 (fn-ast-xref-one it)) :pair)
              (and (consp (mv-nth 1 (fn-ast-xref-one it)))
                   (stringp (car (mv-nth 1 (fn-ast-xref-one it))))))
     :hints (("Goal" :use fn-ast-xref-one-pair-is-numbered
                     :in-theory (disable fn-ast-xref-one))))))

; The render transition keeps the cursor invariant, so a cursor made by
; fn-ast-ready-memberships stays a valid guard argument for every later unit.
(defthm fn-ast-render-one-keeps-cursorp
  (implies (fn-ast-cursorp cur fn-arena)
           (fn-ast-cursorp (mv-nth 1 (fn-ast-render-one cur fn-arena)) fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-ast-render-one fn-ast-cursorp fn-ast-at
                                   fn-npw-piecesp fn-npw-partp)
                                  (fn-npw-one fn-ast-xref-one fn-npw-one-keeps-pieces
                                   fn-ast-server-one fn-ast-server-statep fn-ast-xref-pairsp))
                  :use ((:instance fn-npw-one-keeps-pieces
                          (pieces (fn-ast-at 1 cur)) (pos (nfix (fn-ast-at 2 cur))))))))

(local
 (defthm fn-ast-at-of-cons
   (implies (natp i)
            (equal (fn-ast-at i (cons a b))
                   (if (zp i) a (fn-ast-at (- i 1) b))))
   :hints (("Goal" :expand ((fn-ast-at i (cons a b)))))))

(local
 (defthm fn-ast-initial-pieces-piecesp
   (fn-npw-piecesp (fn-ast-initial-pieces kind number article) fn-arena)
   :hints (("Goal" :in-theory (enable fn-ast-initial-pieces fn-npw-piecesp fn-npw-partp)))))

; The cursor the owner publishes is always a valid cursor, whatever the capture holds.
(defthm fn-ast-ready-memberships-cursorp
  (fn-ast-cursorp (fn-ast-ready-memberships scan kind number article server) fn-arena)
  :hints (("Goal" :in-theory (e/d (fn-ast-ready-memberships fn-ast-ready fn-ast-cursorp
                                   fn-ast-server-statep fn-ast-srv-tailp fn-ast-server-state
                                   fn-ast-xref-state)
                                  (fn-ast-initial-pieces fn-ast-at)))))

; A window retains an emitted fragment separately from the immutable cursor.
; A transition or a quantum may produce more octets than the window has room
; for; none is lost: the window keeps them and the next call sends them first.
(defun fn-ast-window-cur (window)
  (declare (xargs :guard t))
  (if (eq (fn-ast-at 0 window) :window) (fn-ast-at 2 window) window))

(defun fn-ast-window-pending (window)
  (declare (xargs :guard t))
  (and (eq (fn-ast-at 0 window) :window) (fn-ast-at 1 window)))

(defun fn-ast-window-donep (window)
  (declare (xargs :guard t))
  (and (not (consp (fn-ast-window-pending window)))
       (eq (fn-ast-at 0 (fn-ast-window-cur window)) :done)))

(defun fn-ast-windowp (window fn-arena)
  (declare (xargs :stobjs fn-arena :guard t))
  (and (fn-ast-cursorp (fn-ast-window-cur window) fn-arena)
       (fn-cbor-octet-listp (fn-ast-window-pending window))))

(local
 (defthm fn-ast-window-cur-of-ready-memberships
   (equal (fn-ast-window-cur (fn-ast-ready-memberships scan kind number article server))
          (fn-ast-ready-memberships scan kind number article server))
   :hints (("Goal" :in-theory (e/d (fn-ast-window-cur fn-ast-ready-memberships fn-ast-ready fn-ast-at)
                                   (fn-ast-cursorp fn-ast-initial-pieces))))))

; The cursor the owner publishes is a window in the sense of the render guard.
(local
 (defthm fn-ast-window-pending-of-ready-memberships
   (equal (fn-ast-window-pending (fn-ast-ready-memberships scan kind number article server))
          nil)
   :hints (("Goal" :in-theory (e/d (fn-ast-window-pending fn-ast-ready-memberships fn-ast-ready fn-ast-at)
                                   (fn-ast-cursorp fn-ast-initial-pieces))))))

(defthm fn-ast-ready-memberships-windowp
  (fn-ast-windowp (fn-ast-ready-memberships scan kind number article server) fn-arena)
  :hints (("Goal" :in-theory (e/d (fn-ast-windowp) (fn-ast-ready-memberships fn-ast-window-pending)))))

;; THE WINDOW RENDER.  A window is (:window PENDING CUR): PENDING octets
;; emitted but not yet sent, CUR the cursor.  One call clears the output buffer
;; and writes at most OCTETS octets into it, spending one unit of FUEL per
;; pending octet sent, per cursor transition and per payload quantum.
;;
;; The payload phase is rendered a quantum at a time over spans: the next
;; window of the payload (no more octets than the room left) is loaded into the
;; workspace (`fn-ast-load', A-ARENA-SPAN-INTO for a handle) and streamed by
;; `fn-nsp-stuff' (books/nntp-spans.lisp: each line dot-stuffed, ".CRLF" after
;; the last), LAST when the window reaches the payload's end.  The stream's
;; state (0 at a line start) is the cursor's line-start flag; the octets it
;; consumed advance the source.  The stream needs three octets of room (its
;; floor, ".CRLF"); a call left with less room offers three and keeps the
;; octets past its bound as PENDING, so no window is ever written past OCTETS
;; and none stalls (F4 of the step 3 packet).  A refused stream (an
;; unterminated last line, which a valid preflight excludes) ends the cursor.
(defun fn-ast-out-tail (i end fn-dss-out)
  (declare (xargs :stobjs fn-dss-out
                  :guard (and (natp i) (natp end) (<= end (fn-dss-out-len fn-dss-out)))
                  :measure (nfix (- (nfix end) (nfix i)))))
  (if (and (natp i) (natp end) (< i end))
      (cons (fn-dss-out-get i fn-dss-out) (fn-ast-out-tail (+ 1 i) end fn-dss-out))
    nil))

; The octets past BOUND are taken out of the buffer and kept (at most two:
; only a window with less room than the stream's floor of three has any).
(defun fn-ast-split-excess (bound fn-dss-out)
  (declare (xargs :stobjs fn-dss-out :guard (natp bound)))
  (let ((len (fn-dss-out-len fn-dss-out)))
    (if (< bound len)
        (let* ((pending (fn-ast-out-tail bound len fn-dss-out))
               (fn-dss-out (fn-dss-out-truncate bound fn-dss-out)))
          (mv pending fn-dss-out))
      (mv nil fn-dss-out))))

(defthm fn-ast-word-octets-octets
  (fn-cbor-octet-listp (fn-oct-word-octets w k))
  :hints (("Goal" :in-theory (enable fn-oct-word-octets fn-cbor-octet-listp))))
(defthm fn-ast-stuff-list-loop-octets
  (fn-cbor-octet-listp (mv-nth 2 (fn-nsp-stuff-list-loop s xs last room)))
  :hints (("Goal" :induct (fn-nsp-stuff-list-loop s xs last room)
           :in-theory (enable fn-nsp-stuff-list-loop))))
(defthm fn-ast-stuff-list-octets
  (fn-cbor-octet-listp (mv-nth 2 (fn-nsp-stuff-list s xs last room)))
  :hints (("Goal" :in-theory (enable fn-nsp-stuff-list))))

(defthm fn-ast-nth-octet
  (implies (and (fn-cbor-octet-listp xs) (natp i) (< i (len xs)))
           (fn-cbor-octetp (nth i xs)))
  :hints (("Goal" :in-theory (enable fn-cbor-octet-listp nth))))
(defthm fn-ast-out-tail-octets
  (implies (and (fn-cbor-octet-listp fn-dss-out) (<= end (len fn-dss-out)))
           (fn-cbor-octet-listp (fn-ast-out-tail i end fn-dss-out)))
  :hints (("Goal" :in-theory (e/d (fn-cbor-octet-listp fn-dss-out-get) (fn-cbor-octetp)))))
(defthm fn-ast-split-excess-len
  (implies (and (natp bound) (true-listp fn-dss-out))
           (and (true-listp (mv-nth 1 (fn-ast-split-excess bound fn-dss-out)))
                (equal (len (mv-nth 1 (fn-ast-split-excess bound fn-dss-out)))
                       (min bound (len fn-dss-out)))))
  :hints (("Goal" :in-theory (e/d (fn-oct-take) (fn-ast-out-tail)))))

(defthm fn-ast-stuff-call-len
  (implies (and (natp cap) (true-listp fn-dss-out))
           (let ((out2 (mv-nth 3 (fn-nsp-stuff s 0 end last cap fn-octets fn-dss-out))))
             (and (true-listp out2) (<= (len fn-dss-out) (len out2)))))
  :hints (("Goal" :in-theory (disable fn-nsp-stuff-list))))

(defthm fn-ast-split-excess-facts
  (implies (and (natp bound) (fn-cbor-octet-listp fn-dss-out))
           (and (fn-cbor-octet-listp (car (fn-ast-split-excess bound fn-dss-out)))
                (fn-cbor-octet-listp (mv-nth 1 (fn-ast-split-excess bound fn-dss-out)))
                (equal (len (mv-nth 1 (fn-ast-split-excess bound fn-dss-out)))
                       (min bound (len fn-dss-out)))))
  :hints (("Goal" :in-theory (e/d (fn-oct-take) (fn-ast-out-tail)))))
(defthm fn-ast-stuff-call-facts
  (implies (and (natp cap) (fn-cbor-octet-listp fn-dss-out)
                (natp end) (<= end (len fn-octets)))
           (let ((out2 (mv-nth 3 (fn-nsp-stuff s 0 end last cap fn-octets fn-dss-out))))
             (and (fn-cbor-octet-listp out2)
                  (<= (len fn-dss-out) (len out2)))))
  :hints (("Goal" :in-theory (disable fn-nsp-stuff-list))))

(defun fn-ast-payload-quantum (cur left fn-arena fn-ast-ws fn-dss-out)
  (declare (xargs :stobjs (fn-arena fn-ast-ws fn-dss-out)
                  :guard (and (natp left) (<= left *fn-ast-window-max*)
                              (<= (fn-dss-out-len fn-dss-out) *fn-ast-window-max*))
                  :guard-hints (("Goal" :do-not-induct t
                                 :in-theory (disable fn-nsp-stuff fn-ast-load fn-ast-source-avail
                                                     fn-ast-at fn-ast-out-tail fn-ast-source-advance
                                                     fn-nsp-stuff-writes fn-nsp-stuff-is-list
                                                     fn-ast-load-is-window)
                                 :use ((:instance fn-nsp-stuff-writes
                                        (s (if (fn-ast-at 5 cur) 0 1)) (i 0)
                                        (end (min (min left (fn-ast-source-avail (fn-ast-at 4 cur) fn-arena))
                                                  (len (fn-ast-load (fn-ast-at 4 cur)
                                                                    (min left (fn-ast-source-avail (fn-ast-at 4 cur) fn-arena))
                                                                    fn-arena fn-ast-ws))))
                                        (last (equal (min (min left (fn-ast-source-avail (fn-ast-at 4 cur) fn-arena))
                                                          (len (fn-ast-load (fn-ast-at 4 cur)
                                                                            (min left (fn-ast-source-avail (fn-ast-at 4 cur) fn-arena))
                                                                            fn-arena fn-ast-ws)))
                                                     (nfix (fn-ast-at 2 (fn-ast-at 4 cur)))))
                                        (cap (+ (len fn-dss-out) (max left 3)))
                                        (fn-octets (fn-ast-load (fn-ast-at 4 cur)
                                                                (min left (fn-ast-source-avail (fn-ast-at 4 cur) fn-arena))
                                                                fn-arena fn-ast-ws))))))))
  (let* ((source (fn-ast-at 4 cur))
         (rem (nfix (fn-ast-at 2 source)))
         (n (fn-ast-source-take source left fn-arena))
         (fn-ast-ws (fn-ast-load source n fn-arena fn-ast-ws))
         (m (min n (fn-ast-ws-len fn-ast-ws)))
         (lastp (eql m rem))
         (s (if (fn-ast-at 5 cur) 0 1))
         (base (fn-dss-out-len fn-dss-out))
         (cap (+ base (max left 3))))
    (if (and (zp m) (not lastp))
        (mv nil (list :done nil 0 nil nil nil nil) 0 fn-ast-ws fn-dss-out)
      (mv-let (r s2 i2 fn-dss-out)
        (fn-nsp-stuff s 0 m lastp cap fn-ast-ws fn-dss-out)
        (mv-let (pending fn-dss-out) (fn-ast-split-excess (+ base left) fn-dss-out)
          (let* ((next (if (or (eq r :done) (eq r :refused))
                         (list :done nil 0 nil nil nil nil)
                       (list :payload nil 0 nil (fn-ast-source-advance source (nfix i2)) (eql s2 0) nil))))
          (mv pending next (- (fn-dss-out-len fn-dss-out) base) fn-ast-ws fn-dss-out)))))))

(defthm fn-ast-payload-quantum-facts
  (implies (and (natp left) (<= left *fn-ast-window-max*)
                (fn-cbor-octet-listp fn-dss-out) (<= (len fn-dss-out) *fn-ast-window-max*))
           (mv-let (pending next used ws out)
             (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)
             (declare (ignore ws pending))
             (and (fn-cbor-octet-listp (car (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                  (natp used) (<= used left)
                  (equal (len out) (+ (len fn-dss-out) used))
                  (fn-cbor-octet-listp out)
                  (fn-ast-cursorp next fn-arena))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ast-cursorp)
                           (fn-ast-load fn-ast-source-avail fn-ast-at fn-ast-split-excess
                            fn-ast-source-advance fn-nsp-stuff fn-nsp-stuff-is-list fn-ast-load-is-window)))))

(defthm fn-ast-payload-quantum-used-bound
  (implies (and (natp left) (<= left *fn-ast-window-max*)
                (true-listp fn-dss-out) (<= (len fn-dss-out) *fn-ast-window-max*))
           (and (<= 0 (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                (<= (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)) left)
                (integerp (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                (true-listp (mv-nth 4 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                (equal (len (mv-nth 4 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                       (+ (len fn-dss-out)
                          (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out))))))
  :rule-classes ((:linear :corollary
                  (implies (and (natp left) (<= left *fn-ast-window-max*)
                                (true-listp fn-dss-out) (<= (len fn-dss-out) *fn-ast-window-max*))
                           (and (<= 0 (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                                (<= (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)) left))))
                 (:rewrite :corollary
                  (implies (and (natp left) (<= left *fn-ast-window-max*)
                                (true-listp fn-dss-out) (<= (len fn-dss-out) *fn-ast-window-max*))
                           (and (integerp (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                                (true-listp (mv-nth 4 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                                (equal (len (mv-nth 4 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)))
                                       (+ (len fn-dss-out)
                                          (mv-nth 2 (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out))))))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-ast-cursorp)
                           (fn-ast-load fn-ast-source-avail fn-ast-at fn-ast-split-excess
                            fn-ast-source-advance fn-nsp-stuff fn-nsp-stuff-is-list fn-ast-load-is-window)))))

(defun fn-ast-render-window-aux (cur pending fuel left fn-arena fn-ast-ws fn-dss-out)
  (declare (xargs :stobjs (fn-arena fn-ast-ws fn-dss-out) :measure (nfix fuel)
                  :guard (and (fn-ast-cursorp cur fn-arena) (fn-cbor-octet-listp pending)
                              (natp fuel) (natp left) (<= left *fn-ast-window-max*)
                              (<= (+ left (fn-dss-out-len fn-dss-out)) *fn-ast-window-max*))
                  :verify-guards nil))
  (cond
   ((or (zp fuel) (zp left)
        (and (not (consp pending)) (eq (fn-ast-at 0 cur) :done)))
    (mv (list :window pending cur) fn-ast-ws fn-dss-out))
   ((consp pending)
    (let ((fn-dss-out (fn-dss-out-append-octet (car pending) fn-dss-out)))
      (fn-ast-render-window-aux cur (cdr pending) (- fuel 1) (- left 1) fn-arena fn-ast-ws fn-dss-out)))
   ((and (eq (fn-ast-at 0 cur) :payload) (not (consp (fn-ast-at 1 cur))))
    (mv-let (pending2 next used fn-ast-ws fn-dss-out)
      (fn-ast-payload-quantum cur left fn-arena fn-ast-ws fn-dss-out)
      (fn-ast-render-window-aux next pending2 (- fuel 1) (nfix (- left used))
                                fn-arena fn-ast-ws fn-dss-out)))
   (t
    (mv-let (out next) (fn-ast-render-one cur fn-arena)
      (fn-ast-render-window-aux next out (- fuel 1) left fn-arena fn-ast-ws fn-dss-out)))))

(local
 (defthm fn-ast-snoc-octets
   (implies (and (fn-cbor-octet-listp xs) (fn-cbor-octetp o))
            (and (fn-cbor-octet-listp (fn-oct-snoc xs o))
                 (equal (len (fn-oct-snoc xs o)) (+ 1 (len xs)))))
   :hints (("Goal" :in-theory (enable fn-oct-snoc fn-cbor-octet-listp)))))

(local
 (defthm fn-ast-render-one-output-octets
   (implies (fn-ast-cursorp cur fn-arena)
            (fn-cbor-octet-listp (car (fn-ast-render-one cur fn-arena))))
   :hints (("Goal" :in-theory (e/d (fn-ast-render-one fn-ast-cursorp)
                                   (fn-npw-one fn-ast-xref-one fn-ast-server-one fn-npw-piecesp
                                    fn-npw-one-output-octets))
                   :use ((:instance fn-npw-one-output-octets
                          (pieces (fn-ast-at 1 cur)) (pos (nfix (fn-ast-at 2 cur)))))))))

; The window invariant, the output's octets and its bound, through every call.
(defthm fn-ast-render-window-aux-facts
  (implies (and (fn-ast-cursorp cur fn-arena) (fn-cbor-octet-listp pending)
                (natp left) (<= left *fn-ast-window-max*)
                (fn-cbor-octet-listp fn-dss-out)
                (<= (+ left (len fn-dss-out)) *fn-ast-window-max*))
           (mv-let (window ws out)
             (fn-ast-render-window-aux cur pending fuel left fn-arena fn-ast-ws fn-dss-out)
             (declare (ignore ws))
             (and (fn-ast-windowp window fn-arena)
                  (fn-cbor-octet-listp out)
                  (<= (len out) (+ (len fn-dss-out) left)))))
  :hints (("Goal" :induct (fn-ast-render-window-aux cur pending fuel left fn-arena fn-ast-ws fn-dss-out)
           :in-theory (e/d (fn-ast-windowp fn-ast-window-cur fn-ast-window-pending fn-ast-at)
                           (fn-ast-payload-quantum fn-ast-render-one fn-ast-cursorp))
           :expand ((fn-ast-render-window-aux cur pending fuel left fn-arena fn-ast-ws fn-dss-out)))))

(verify-guards fn-ast-render-window-aux
  :hints (("Goal" :in-theory (disable fn-ast-payload-quantum fn-ast-render-one fn-ast-cursorp))))

(defun fn-ast-render-window (window fuel octets fn-arena fn-ast-ws fn-dss-out)
  (declare (xargs :stobjs (fn-arena fn-ast-ws fn-dss-out)
                  :guard (fn-ast-windowp window fn-arena)
                  :guard-hints (("Goal" :in-theory (enable fn-ast-windowp)))))
  (let ((fn-dss-out (fn-dss-out-clear fn-dss-out)))
    (fn-ast-render-window-aux (fn-ast-window-cur window) (fn-ast-window-pending window)
                              (nfix fuel) (min (nfix octets) *fn-ast-window-max*)
                              fn-arena fn-ast-ws fn-dss-out)))

(defthm fn-ast-render-window-aux-len
  (implies (and (natp left) (<= left *fn-ast-window-max*) (true-listp fn-dss-out)
                (<= (+ left (len fn-dss-out)) *fn-ast-window-max*))
           (let ((out (mv-nth 2 (fn-ast-render-window-aux cur pending fuel left fn-arena fn-ast-ws fn-dss-out))))
             (and (true-listp out) (<= (len out) (+ (len fn-dss-out) left)))))
  :hints (("Goal" :induct (fn-ast-render-window-aux cur pending fuel left fn-arena fn-ast-ws fn-dss-out)
           :in-theory (e/d (fn-oct-snoc) (fn-ast-payload-quantum fn-ast-render-one fn-ast-cursorp)))))

; A window rendered from a valid window is a valid window, so the plan can
; carry it; and no call writes more than OCTETS octets.
(defthm fn-ast-render-window-keeps-windowp
  (implies (fn-ast-windowp window fn-arena)
           (fn-ast-windowp (mv-nth 0 (fn-ast-render-window window fuel octets fn-arena fn-ast-ws fn-dss-out))
                           fn-arena))
  :hints (("Goal" :in-theory (e/d (fn-ast-windowp) (fn-ast-render-window-aux fn-ast-window-cur fn-ast-window-pending))
                  :use ((:instance fn-ast-render-window-aux-facts
                         (cur (fn-ast-window-cur window)) (pending (fn-ast-window-pending window))
                         (fuel (nfix fuel)) (left (min (nfix octets) *fn-ast-window-max*))
                         (fn-dss-out nil))))))

(defthm fn-ast-render-window-byte-bound
  (<= (len (mv-nth 2 (fn-ast-render-window window fuel octets fn-arena fn-ast-ws fn-dss-out)))
      (nfix octets))
  :rule-classes :linear
  :hints (("Goal" :in-theory (disable fn-ast-render-window-aux fn-ast-window-cur fn-ast-window-pending)
                  :use ((:instance fn-ast-render-window-aux-len
                         (cur (fn-ast-window-cur window)) (pending (fn-ast-window-pending window))
                         (fuel (nfix fuel)) (left (min (nfix octets) *fn-ast-window-max*))
                         (fn-dss-out nil))))))

;; The served path's runs, for the keystones: K preflight quanta, and K window
;; calls with every call's output collected in order.
(defun fn-ast-scan-run (scan fuel k fn-arena fn-ast-ws)
  (declare (xargs :stobjs (fn-arena fn-ast-ws) :guard (and (natp fuel) (natp k))
                  :verify-guards nil))
  (if (zp k)
      (mv scan fn-ast-ws)
    (mv-let (scan fn-ast-ws) (fn-ast-scan-step scan fuel fn-arena fn-ast-ws)
      (fn-ast-scan-run scan fuel (- k 1) fn-arena fn-ast-ws))))

(defun fn-ast-render-run (window fuel octets k fn-arena fn-ast-ws fn-dss-out)
  (declare (xargs :stobjs (fn-arena fn-ast-ws fn-dss-out) :guard (and (natp fuel) (natp k))
                  :verify-guards nil))
  (if (zp k)
      (mv window nil fn-ast-ws fn-dss-out)
    (mv-let (w2 fn-ast-ws fn-dss-out)
      (fn-ast-render-window window fuel octets fn-arena fn-ast-ws fn-dss-out)
      (let ((sent (fn-dss-out-list fn-dss-out)))
        (mv-let (w3 rest fn-ast-ws fn-dss-out)
          (fn-ast-render-run w2 fuel octets (- k 1) fn-arena fn-ast-ws fn-dss-out)
          (mv w3 (append sent rest) fn-ast-ws fn-dss-out))))))
