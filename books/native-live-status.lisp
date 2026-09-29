; fn: the operator's status report, one renderer for the offline store and
; the running owner, and the local-control exchange that carries it.
;
; `operator CONFIG status' (and `pins', `obligations', `peer list') used to
; open the Store, so while an owner held it the answer was `store is already
; locked' (planning/evidence/spike-operator-2026-09-25.md).  The report is
; now one ACL2 function of the Store state, the carried profile, the
; configuration, the open connections' configuration pins and the host's
; open-time observations (`fn-nls-report').  The offline command applies it
; to the state it just replayed (`fn-nls-offline-report'); the running owner
; applies it to the state it carries (`fn-nls-live-report') and sends it
; over the control socket in pages (`fn-nls-reply'), which the client joins
; (`fn-nls-client-step').  The two keystones:
;
;   fn-nls-live-report-is-the-offline-report   the owner's words are the
;       offline words of the same state (carried octet sum valid, no open
;       connection, the view current: PKT-885, the counts are the view's);
;   fn-nls-client-step-of-owner-reply          every page of a report
;       extends the client's prefix of the one report, to the whole report;
;   fn-nls-client-step-of-owner-page           the same of the page the
;       owner answers from the report it rendered once per request
;       (`fn-nls-page-of-buffer-is-reply', the string twin).
;
; Answering changes no state: the owner's entry (host/native-live-status-
; host.lisp `fn-native-live-status-host-answer') takes `state' and returns a
; single value (the page and the rendered buffers, which the host carries),
; so ACL2 admits no update of it, and unlike
; `fn-owner-headroom' it extends the carried octet sum without storing it.
;
; Representation (D27): the owner pages from a string buffer rendered once
; per request (`fn-nls-page', proved equal to the octet-list page).  The
; renderer and both frames are still octet lists, like the rest of the FNCT
; control codec; their twin is open.
;
; This book owns the prefix `fn-nls-' (docs/prefixes.md).

(in-package "ACL2")
(include-book "native-control")
(include-book "native-admin")
(include-book "accounts")
; PKT-391: `account list' names each row kind.
(include-book "account-list")
(include-book "store-budget")
; PKT-169: the maintenance reservation `status' prints.
(include-book "store-capacity-vector")
(include-book "owner-config")
(include-book "store-reclaim-holders")
(include-book "records-stamp")

;; The tau system is off in this book (lane tau-pass, tools/tau_cost.py).
;; Its work is proof time no prover step counts (docs/proof-style.md
;; 9.1); planning/evidence/tau-cost-*.json has this book's figures.
(local (in-theory (disable (tau-system))))

; -----------------------------------------------------------------------------
; Words

(defun fn-nls-text (text)
  (declare (xargs :guard t))
  (fn-record-string-octets text))

; Every natural in decimal.  The renderer was `fn-nntp-decimal-field', the
; NNTP response renderer, which answers 0 past ten digits (RFC 3977 section
; 6 bounds what it renders); a status value is the operator's and has no
; such bound, so any value of 2^34 or more (eleven digits), the default
; max-history-octets 2^40 among them, printed 0 (PKT-156).
(defun fn-nls-digits (n acc)
  (declare (xargs :guard (natp n)
                  :measure (nfix n)
                  :hints (("Goal" :in-theory (disable floor mod)))))
  (if (zp n)
      acc
    (fn-nls-digits (floor n 10) (cons (+ 48 (mod n 10)) acc))))

(defun fn-nls-nat (n)
  (declare (xargs :guard t))
  (if (posp n) (fn-nls-digits n nil) '(48)))

(defthm fn-nls-digits-true-listp
  (implies (true-listp acc) (true-listp (fn-nls-digits n acc)))
  :rule-classes :type-prescription
  :hints (("Goal" :in-theory (disable floor mod))))

(defthm fn-nls-nat-true-listp
  (true-listp (fn-nls-nat n))
  :rule-classes :type-prescription)

(encapsulate ()
(local
 (defthm fn-nls-digits-of-append
   (equal (fn-nls-digits n (append x y))
          (append (fn-nls-digits n x) y))
   :hints (("Goal" :induct (fn-nls-digits n x) :in-theory (disable floor mod)))))
(local
 (defthm fn-nls-digits-is-append
   (implies (syntaxp (not (equal acc ''nil)))
            (equal (fn-nls-digits n acc)
                   (append (fn-nls-digits n nil) acc)))
   :hints (("Goal" :use ((:instance fn-nls-digits-of-append (x nil) (y acc)))
            :in-theory (disable fn-nls-digits-of-append floor mod)))))
(local
 (defthm fn-nls-value-aux-of-append
   (equal (fn-nntp-decimal-value-aux (append x y) a)
          (fn-nntp-decimal-value-aux y (fn-nntp-decimal-value-aux x a)))
   :hints (("Goal" :induct (fn-nntp-decimal-value-aux x a)
            :in-theory (enable fn-nntp-decimal-value-aux)))))
(local
 (defthm fn-nls-digits-value
   (implies (natp n)
            (equal (fn-nntp-decimal-value-aux (fn-nls-digits n nil) 0) n))
   :hints (("Goal" :induct (fn-nls-digits n nil)
            :in-theory (e/d (fn-nntp-decimal-value-aux mod) (floor))))))
(local
 (encapsulate ()
   (local (include-book "arithmetic-5/top" :dir :system))
   (defthm fn-nls-mod-10-is-a-digit
     (implies (natp n)
              (and (<= 0 (mod n 10)) (< (mod n 10) 10)))
     :rule-classes :linear)
   (defthm fn-nls-mod-10-integer
     (implies (natp n) (integerp (mod n 10)))
     :rule-classes :type-prescription)))
(local
 (defthm fn-nls-tokenp-of-append
   (equal (fn-nntp-decimal-tokenp (append x y))
          (and (fn-nntp-decimal-tokenp x) (fn-nntp-decimal-tokenp y)))
   :hints (("Goal" :in-theory (enable fn-nntp-decimal-tokenp)))))
(local
 (defthm fn-nls-digits-tokenp
   (implies (natp n)
            (fn-nntp-decimal-tokenp (fn-nls-digits n nil)))
   :hints (("Goal" :induct (fn-nls-digits n nil)
            :in-theory (e/d (fn-nntp-decimal-tokenp fn-nntp-decimal-digitp)
                            (floor mod))))))
(local
 (defthm fn-nls-digits-consp
   (implies (posp n) (consp (fn-nls-digits n nil)))
   :hints (("Goal" :expand ((fn-nls-digits n nil)) :in-theory (disable floor mod)))))
; KEYSTONE (PKT-156).  The words status prints for every natural are its
; decimal digits: a nonempty run of digits whose value, read by the NNTP
; decimal reader `fn-nntp-decimal-value', is the natural itself, however
; many digits it has.  Every number of the report goes through
; `fn-nls-nat' (`fn-nls-field', `fn-nls-value'), which
; `fn-native-live-status-host-offline' (host/native/io.lisp
; `fnn-command-live-report') and `fn-native-live-status-host-answer'
; (host/native/control.lisp `fnn-control-live-status-answer') reach.
(defthm fn-nls-nat-is-the-decimal-digits
  (implies (natp n)
           (and (consp (fn-nls-nat n))
                (fn-nntp-decimal-tokenp (fn-nls-nat n))
                (equal (fn-nntp-decimal-value (fn-nls-nat n)) n)))
  :hints (("Goal" :in-theory (enable fn-nls-nat fn-nntp-decimal-value fn-nntp-decimal-tokenp
                                     fn-nntp-decimal-value-aux fn-nntp-decimal-digitp)))))

(defun fn-nls-value (v)
  "A reported value: a word or a natural."
  (declare (xargs :guard t))
  (if (stringp v) (fn-nls-text v) (fn-nls-nat v)))

(defthm fn-nls-value-true-listp
  (true-listp (fn-nls-value v))
  :rule-classes :type-prescription)

(in-theory (disable fn-nls-nat fn-nls-value))

(defconst *fn-nls-lf* '(10))

(defun fn-nls-field (name n)
  "` NAME=N'."
  (declare (xargs :guard t))
  (append (fn-nls-text " ") (fn-nls-text name) (fn-nls-text "=") (fn-nls-value n)))

(defun fn-nls-profile-words (report)
  "The `fn-bs-profile-report' pairs as ` NAME=VALUE' words, in its order."
  (declare (xargs :guard t))
  (if (consp report)
      (append (if (consp (car report))
                  (fn-nls-field (car (car report)) (cdr (car report)))
                nil)
              (fn-nls-profile-words (cdr report)))
    nil))

; The pessimistic open cost of the profile, printed beside its values
; (planning/design-2026-09-25-bounds.md sections 3.3 and 4; PKT-105).  The
; worst open is a full replay: a checkpoint may be absent or refused, and
; then every committed record is read, at most max-transactions of them.
; Its memory is the record payloads as octet lists: two long-lived copies,
; 16 octets of cons per payload octet on a 64-bit SBCL, so 32 per octet of
; max-history-octets.  Both are what the profile admits, not what the Store
; holds (`headroom' carries that) nor what an open measured.
(defconst *fn-nls-open-list-octets-per-octet* 32)

(defun fn-nls-open-cost-words (profile)
  "`open-cost replay-records=T list-memory-octets=M', M = 32 H."
  (declare (xargs :guard t))
  (append (fn-nls-text "open-cost")
          (fn-nls-field "replay-records" (fn-bs-profile-max-transactions profile))
          (fn-nls-field "list-memory-octets"
                        (* *fn-nls-open-list-octets-per-octet*
                           (nfix (fn-bs-profile-max-history-octets profile))))))

(defun fn-nls-names (names)
  (declare (xargs :guard t))
  (if (consp names)
      (append (fn-nls-text (car names))
              (if (consp (cdr names)) (fn-nls-text " ") nil)
              (fn-nls-names (cdr names)))
    nil))

; OBS is the host's observation, carried unchanged:
;   (ORPHANS MOREP MODE CHECKPOINT-FILE), ORPHANS the staging names the sweep
;   found at its own open, MOREP whether it stopped at its bound, MODE
;   (:checkpoint G S) or (:full-replay REASON), and CHECKPOINT-FILE the
;   lstat of the newest published state checkpoint when the report is asked
;   for: (OCTETS MODIFIED), or nil when there is none.
(defun fn-nls-obs-orphans (obs) (declare (xargs :guard t)) (fn-ag-car obs))
(defun fn-nls-obs-morep (obs) (declare (xargs :guard t)) (fn-ag-car (fn-ag-cdr obs)))
(defun fn-nls-obs-mode (obs)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr obs))))

(defun fn-nls-obs-checkpoint-file (obs)
  ; The fifth element: the clock observation (fn-nls-obs-clock) is the fourth.
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr obs))))))

(defun fn-nls-reason-words (reason)
  (declare (xargs :guard t))
  (if (and (symbolp reason)
           (standard-char-listp (coerce (symbol-name reason) 'list)))
      (fn-nls-text (string-downcase (symbol-name reason)))
    (fn-nls-text "unknown")))

; The sixth element: the owner's deferred automatic publication,
; (:deferred REASON ESTIMATE BOUND) as books/owner-checkpoint-pipeline.lisp
; `fn-ockp-decide' answered it (REASON exceeds-budget or exceeds-space) and host/owner-host.lisp
; `fn-owner-sco-publication-done' recorded it (host/native-live-status-host.lisp
; appends it to the host's observation); nil when nothing is deferred, and
; always nil offline (no owner, no publisher).
(defun fn-nls-obs-checkpoint-deferred (obs)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr obs)))))))

(defun fn-nls-checkpoint-deferred-words (obs)
  "` deferred=REASON estimate=E budget=B' while the owner's automatic
publication is deferred (PKT-492: the file it would write, E octets, is past
the profile's checkpoint budget B, so nothing was encoded and the owner keeps
serving; the publication is retried when the budget covers E); nothing
otherwise, so every other report is byte-identical."
  (declare (xargs :guard t))
  (let ((d (fn-nls-obs-checkpoint-deferred obs)))
    (if (and (consp d) (equal (fn-ag-car d) :deferred))
        (append (fn-nls-text " deferred=")
                (fn-nls-reason-words (fn-ag-car (fn-ag-cdr d)))
                (fn-nls-field "estimate" (fn-ag-car (fn-ag-cdr (fn-ag-cdr d))))
                (fn-nls-field "budget" (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr d))))))
      nil)))

(defun fn-nls-checkpoint-file-words (obs)
  "`checkpoint-file octets=N modified=T', or `checkpoint-file=absent', then
the deferred words when the owner deferred its publication.  While an owner
runs it is the only publisher (the verb needs the Store lock), so after a
run this is the owner's last automatic publication; the `open=' line says
whether a checkpoint served this process's open."
  (declare (xargs :guard t))
  (let ((file (fn-nls-obs-checkpoint-file obs)))
    (append (if (consp file)
                (append (fn-nls-text "checkpoint-file")
                        (fn-nls-field "octets" (fn-ag-car file))
                        (fn-nls-field "modified" (fn-ag-car (fn-ag-cdr file))))
              (fn-nls-text "checkpoint-file=absent"))
            (fn-nls-checkpoint-deferred-words obs))))

(defun fn-nls-orphan-words (obs)
  "`staging-orphans=N[+] [NAME ...]', or `staging-orphans=0'."
  (declare (xargs :guard t))
  (let ((names (fn-nls-obs-orphans obs)))
    (if (consp names)
        (append (fn-nls-text "staging-orphans=") (fn-nls-nat (len names))
                (if (fn-nls-obs-morep obs) (fn-nls-text "+") nil)
                (fn-nls-text " [") (fn-nls-names names) (fn-nls-text "]"))
      (fn-nls-text "staging-orphans=0"))))

(defun fn-nls-open-words (obs)
  "`open=checkpoint:G suffix=S' or `open=full-replay reason=R'."
  (declare (xargs :guard t))
  (let ((mode (fn-nls-obs-mode obs)))
    (if (equal (fn-ag-car mode) :checkpoint)
        (append (fn-nls-text "open=checkpoint:")
                (fn-nls-nat (fn-ag-car (fn-ag-cdr mode)))
                (fn-nls-field "suffix" (fn-ag-car (fn-ag-cdr (fn-ag-cdr mode)))))
      (append (fn-nls-text "open=full-replay reason=")
              (fn-nls-reason-words (fn-ag-car (fn-ag-cdr mode)))))))

;   (fourth) the clock observation the host read for this report, from
;   which `fn-record-stamp-of-observation' derives the instant a
;   release-after rule is measured at (the same derivation that stamps an
;   article); an unusable clock reclaims nothing under release-after.
(defun fn-nls-obs-clock (obs)
  (declare (xargs :guard t))
  (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr obs)))))

; D13 (STO-014): the retention rule and what it would reclaim now.
(defun fn-nls-rule-words (rule)
  (declare (xargs :guard t))
  (cond ((equal rule '(:released-by-all-holders)) (fn-nls-text "released-by-all-holders"))
        ((and (consp rule) (equal (car rule) :release-after) (consp (cdr rule)))
         (append (fn-nls-text "release-after:") (fn-nls-nat (cadr rule))))
        (t (fn-nls-text "keep-forever"))))

(defun fn-nls-reclaim-words (s cfg obs fn-arena)
  "`reclaim rule=R reclaimable=N reclaimable-octets=N held=N reclaimed=N
freed-octets=N signed=N kept=N'.  PKT-844: reclaimable + held + reclaimed +
signed + kept is the report's articles=N
(`fn-rcl-store-classes-partition-the-articles'); signed counts the articles an
authorship verdict keeps (key statements among them), kept those the rule
keeps."
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let* ((rule (fn-rcl-config-rule (fn-cfg-value cfg)))
         (stamp (fn-record-stamp-of-observation (fn-nls-obs-clock obs)))
         (now (if (natp stamp) stamp nil))
         (counts (fn-rcl-store-counts rule now s fn-arena))
         (classes (fn-rcl-store-classes rule now s fn-arena)))
    (append (fn-nls-text "reclaim rule=") (fn-nls-rule-words rule)
            (fn-nls-field "reclaimable" (nth 0 counts))
            (fn-nls-field "reclaimable-octets" (nth 1 counts))
            (fn-nls-field "held" (nth 4 counts))
            (fn-nls-field "reclaimed" (nth 2 counts))
            (fn-nls-field "freed-octets" (nth 3 counts))
            (fn-nls-field "signed" (nth 0 classes))
            (fn-nls-field "kept" (nth 1 classes)))))

; -----------------------------------------------------------------------------
; The report

(defun fn-nls-headroom-words (headroom)
  (declare (xargs :guard t))
  (append (fn-nls-text "headroom")
          (fn-nls-field "transactions-used" (fn-ag-car headroom))
          (fn-nls-field "transactions-budget" (fn-ag-car (fn-ag-cdr headroom)))
          (fn-nls-field "bytes-used" (fn-ag-car (fn-ag-cdr (fn-ag-cdr headroom))))
          (fn-nls-field "history-bound"
                        (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr headroom)))))
          (fn-nls-field "charge-reserved"
                        (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr headroom))))))
          (fn-nls-field "charge-capacity"
                        (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr
                                                                   (fn-ag-cdr headroom)))))))))

;; PKT-707: the capacity in plain words.  HEADROOM is (USED BUDGET BYTES
;; HISTORY RESERVED CAPACITY) as `fn-sbud-headroom-at' answers it.  The
;; articles left is the transactions left, or, once articles are stored, the
;; history octets left at the average record so far when that is fewer: an
;; estimate, and the line says so.  Zero means the next post is refused.
(defun fn-nls-articles-left (headroom)
  (declare (xargs :guard t))
  (let* ((u (nfix (fn-ag-car headroom)))
         (tb (nfix (fn-ag-car (fn-ag-cdr headroom))))
         (b (nfix (fn-ag-car (fn-ag-cdr (fn-ag-cdr headroom)))))
         (h (nfix (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr headroom))))))
         (tleft (nfix (- tb u)))
         (hleft (nfix (- h b))))
    (cond ((zp tleft) 0)
          ((and (posp u) (posp b))
           (if (zp hleft) 0 (min tleft (floor (* hleft u) b))))
          (t tleft))))

(defthm fn-nls-articles-left-is-at-most-the-transactions-left
  (<= (fn-nls-articles-left headroom)
      (nfix (- (nfix (fn-ag-car (fn-ag-cdr headroom)))
               (nfix (fn-ag-car headroom)))))
  :rule-classes nil)

;; KEYSTONE (the capacity line never promises room that is not there).  At
;; the transaction budget, or with the history bound spent, the line says 0.
(defthm fn-nls-articles-left-is-zero-when-full
  (implies (or (<= (nfix (fn-ag-car (fn-ag-cdr headroom)))
                   (nfix (fn-ag-car headroom)))
               (and (posp (fn-ag-car headroom))
                    (posp (fn-ag-car (fn-ag-cdr (fn-ag-cdr headroom))))
                    (<= (nfix (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr headroom)))))
                        (nfix (fn-ag-car (fn-ag-cdr (fn-ag-cdr headroom)))))))
           (equal (fn-nls-articles-left headroom) 0)))

(defun fn-nls-capacity-words (headroom)
  "`capacity articles-left=N (...)': the line `status' prints under headroom."
  (declare (xargs :guard t))
  (append (fn-nls-text "capacity")
          (fn-nls-field "articles-left" (fn-nls-articles-left headroom))
          (fn-nls-text (if (equal (fn-nls-articles-left headroom) 0)
                           " (full: posts are refused; raise it with store export, then store import --max-transactions N --max-history-octets N; docs/operator.md, When the store is full)"
                         " (an estimate at the average article so far; at 0 posts are refused)"))))

(defun fn-nls-capacity-line (headroom)
  "The capacity line as the host prints it (host/native/io.lisp fnn-out-headroom)."
  (declare (xargs :guard t))
  (fn-nls-capacity-words headroom))

; `maintenance-reserve octets=R transactions=N debt=D held|short' (PRF-138,
; books/store-capacity-vector.lisp `fn-cvec-report'): the room the capacity
; vector keeps, one release record for each of the D open undertakings and
; one for the maintenance release, and whether the committed state has it.
(defun fn-nls-reserve-words (report)
  (declare (xargs :guard t))
  (append (fn-nls-text "maintenance-reserve")
          (fn-nls-field "octets" (fn-ag-car report))
          (fn-nls-field "transactions" (fn-ag-car (fn-ag-cdr report)))
          (fn-nls-field "debt" (fn-ag-car (fn-ag-cdr (fn-ag-cdr report))))
          (if (equal (fn-ag-car (fn-ag-cdr (fn-ag-cdr (fn-ag-cdr report)))) :held)
              (fn-nls-text " held")
            (fn-nls-text " short"))))

; Executes by a loop (lane depth-debt, PRF-919): one line per open
; connection, whose count the operator's max-connections sets (D27: data, not
; a bound).  The right fold runs from the left over the reversed pins.
(defun fn-nls-connection-lines-step (x rest)
  (declare (xargs :guard t :verify-guards nil))
  (append (if (consp x)
              (append (fn-nls-text "connection")
                      (fn-nls-field "id" (car x))
                      (fn-nls-field "config-generation"
                                    (fn-cfg-generation (cdr x)))
                      *fn-nls-lf*)
            nil)
          rest))

(defun fn-nls-connection-lines-loop (rev acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rev)
      (fn-nls-connection-lines-loop (cdr rev) (fn-nls-connection-lines-step (car rev) acc))
    acc))

(defun fn-nls-connection-lines (pins)
  "One `connection id=I config-generation=G' line per open connection's pin
(books/owner-config.lisp: the generation it opened at, or advanced to)."
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp pins)
           (append (if (consp (car pins))
                       (append (fn-nls-text "connection")
                               (fn-nls-field "id" (car (car pins)))
                               (fn-nls-field "config-generation"
                                             (fn-cfg-generation (cdr (car pins))))
                               *fn-nls-lf*)
                     nil)
                   (fn-nls-connection-lines (cdr pins)))
         nil)
       :exec (fn-nls-connection-lines-loop (fn-ag-rev-onto pins nil) nil)))

(defthm fn-nls-connection-lines-loop-of-rev-onto
  (equal (fn-nls-connection-lines-loop (fn-ag-rev-onto pins zs) nil)
         (fn-nls-connection-lines-loop zs (fn-nls-connection-lines pins)))
  :hints (("Goal" :induct (fn-ag-rev-onto pins zs)
                  :in-theory (union-theories
                              '(fn-nls-connection-lines-loop fn-nls-connection-lines fn-nls-connection-lines-step fn-ag-rev-onto
                                car-cons cdr-cons)
                              (union-theories (theory 'minimal-theory)
                                              (executable-counterpart-theory :here))))))


(defun fn-nls-kind-words (kind)
  (declare (xargs :guard t))
  (if (equal kind :forward) (fn-nls-text "forward") (fn-nls-text "archive")))

; PRF-336: one obligation's line, and the lines of a ledger by a loop.  The
; ledger has one obligation per held article, so its length is the Store's
; history; a recursion with one frame per obligation is a stack bound, not a
; work bound.  `fn-nls-obligation-lines' keeps its logical definition and
; executes `fn-nls-obligation-lines-rev' (`mbe', the equation is its guard).
(defun fn-nls-obligation-line (o)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nls-text "obligation id=")
          (fn-nls-text (fn-retain-obligation-id o))
          (fn-nls-text " kind=")
          (fn-nls-kind-words (fn-retain-obligation-kind o))
          (fn-nls-field "charge" (fn-retain-obligation-charge o))
          (fn-nls-text " subject=")
          (fn-nls-text (fn-retain-obligation-subject o))
          *fn-nls-lf*))

(defun fn-nls-obligation-lines-rev (pins acc)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp pins)
      (fn-nls-obligation-lines-rev (cdr pins)
                                   (revappend (fn-nls-obligation-line (car pins)) acc))
    acc))

(defun fn-nls-obligation-lines (pins)
  "One line per held retention obligation, in the ledger's order."
  (declare (xargs :guard t :verify-guards nil))
  (mbe :logic
       (if (consp pins)
           (append (fn-nls-obligation-line (car pins))
                   (fn-nls-obligation-lines (cdr pins)))
         nil)
       :exec (revappend (fn-nls-obligation-lines-rev pins nil) nil)))

(defun fn-nls-retention (s)
  (declare (xargs :guard t :verify-guards nil))
  (fn-node-retention (fn-sn-node s)))

(defun fn-nls-pins-line (s pins)
  (declare (xargs :guard t :verify-guards nil))
  (append (fn-nls-text "pins=")
          (fn-nls-nat (len (fn-retain-pins (fn-nls-retention s))))
          (fn-nls-field "reserved" (fn-retain-reserved (fn-nls-retention s)))
          (fn-nls-field "connections" (len pins))
          *fn-nls-lf*
          (fn-nls-connection-lines pins)))

(defconst *fn-nls-kinds* (quote (:status :pins :peers :obligations :control :health :accounts
                                  :consumers)))

;; PKT-885: the report's `transactions=' and `articles=' counts are SEEN, a
;; pair (TRANSACTIONS . ARTICLES) of the view the report is rendered at, not
;; of the Store state S.  Offline S is the durable state and SEEN its counts
;; (`fn-nls-store-seen'); the running owner renders them from the configured
;; owner's VIEW (`fn-nls-view-seen'), and the host hands it the READER view
;; while a batch is in flight (host/native-live-status-host.lisp
;; `fn-native-live-status-host-answer' passes `fn-ocfg-at-reader-view'; books/
;; owner-reader-view.lisp KEYSTONE fn-ocvm-reader-view-is-the-completed-
;; prefix): a count never includes a record whose barrier has not returned.
;; The capacity, reserve, reclaim and pins lines stay the Store's: they
;; report what the owner has committed to hold, which is conservative while
;; a batch is in flight, and issue no number.
(defun fn-nls-store-seen (s)
  (declare (xargs :guard t))
  (cons (fn-sbud-used s)
        (len (fn-state-articles (fn-node-acceptance (fn-sn-node s))))))

(defun fn-nls-view-seen (view)
  (declare (xargs :guard t))
  (cons (nfix (fn-own-view-version view))
        (len (fn-own-view-raw view))))

(defun fn-nls-counts-words (seen)
  (declare (xargs :guard (consp seen)))
  (append (fn-nls-text "transactions=") (fn-nls-nat (nfix (car seen)))
          (fn-nls-field "articles" (nfix (cdr seen)))))

(defun fn-nls-report (kind profile s bytes seen cfg pins obs fn-arena)
  "The octets `operator CONFIG KIND' prints.

S is the Store state, PROFILE its persisted profile, BYTES its committed
record octets, SEEN the (TRANSACTIONS . ARTICLES) counts of the view the
report is rendered at, CFG the configuration, PINS the open connections'
configuration pins (nil with no owner), OBS the host's open observation."
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (cond
   ((equal kind :peers)
    (fn-native-admin-peer-budget-report (fn-cfg-peers (fn-cfg-value cfg))))
   ((equal kind :control)
    (fn-native-admin-control-report (fn-cfg-authorities (fn-cfg-value cfg))))
   ; PRF-164: `account list' (books/accounts.lisp, no digest or verifier).
   ((equal kind :accounts) (fn-acct-kinds-list-report (fn-cfg-value cfg)))
   ; Row Q10c: `consumer show', the consumer rows' lines alone.
   ((equal kind :consumers) (fn-acct-consumers-list-report (fn-cfg-value cfg)))
   ((equal kind :pins) (fn-nls-pins-line s pins))
   ((equal kind :obligations)
    (append (fn-nls-text "obligations=")
            (fn-nls-nat (len (fn-retain-pins (fn-nls-retention s))))
            (fn-nls-field "reserved" (fn-retain-reserved (fn-nls-retention s)))
            *fn-nls-lf*
            (fn-nls-obligation-lines (fn-retain-pins (fn-nls-retention s)))))
   (t
    (append (fn-nls-counts-words seen)
            (fn-nls-text " ") (fn-nls-orphan-words obs)
            (fn-nls-text " unsigned-legacy-experiment") *fn-nls-lf*
            (fn-nls-text "profile")
            (fn-nls-profile-words (fn-bs-profile-report profile)) *fn-nls-lf*
            (fn-nls-open-cost-words profile) *fn-nls-lf*
            (fn-nls-headroom-words (fn-sbud-headroom-at profile s bytes)) *fn-nls-lf*
            (fn-nls-capacity-words (fn-sbud-headroom-at profile s bytes)) *fn-nls-lf*
            (fn-nls-reserve-words
             (fn-cvec-report profile (fn-sbud-used s) bytes
                             (fn-cvec-record-debt (fn-sf-records (fn-sn-files s)))))
            *fn-nls-lf*
            (fn-nls-open-words obs) *fn-nls-lf*
            (fn-nls-reclaim-words s cfg obs fn-arena) *fn-nls-lf*
            (fn-nls-checkpoint-file-words obs) *fn-nls-lf*
            (fn-nls-pins-line s pins)))))

(defun fn-nls-offline-report (kind profile s cfg obs fn-arena)
  "What the offline command prints over the state it replayed: every
committed record re-encoded once, and no connection."
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (fn-nls-report kind profile s (fn-sbud-bytes-used s) (fn-nls-store-seen s)
                 cfg nil obs fn-arena))

(defun fn-nls-live-report (kind profile oc cache obs fn-arena)
  "What the running owner answers over the configured owner OC it carries:
its Store, its configuration and its connections' pins, with the committed
record octets extended from the carried (K . SUM) CACHE, not stored, and the
counts of the view OC carries (PKT-885: the reader view while a batch is in
flight, which the host puts in place)."
  (declare (xargs :stobjs fn-arena :guard t :verify-guards nil))
  (let ((s (fn-own-store (fn-ocfg-owner oc))))
    (fn-nls-report kind profile s
                   (fn-sbud-bytes-extend cache (fn-sf-records (fn-sn-files s)))
                   (fn-nls-view-seen (fn-own-view (fn-ocfg-owner oc)))
                   (fn-ocfg-config oc) (fn-ocfg-pins oc) obs fn-arena)))

; KEYSTONE (the live words are the offline words).  The subject is
; `fn-nls-live-report', which the owner's control handler reaches through
; host/native-live-status-host.lisp `fn-native-live-status-host-answer'
; (host/native/control.lisp `fnn-control-handle-client'), and
; `fn-nls-offline-report', which `fn-native-live-status-host-offline' calls
; (host/native/io.lisp `fnn-command-live-report').  With the carried octet
; sum valid for the carried records and no connection open, the owner's
; report of every KIND is the offline report of the same Store and
; configuration.  An open connection adds its line; a stale sum changes
; bytes-used; a view behind the Store (a batch in flight) changes the
; counts (tests/acl2/native-live-status-tests.lisp).
(local
 (defthm fn-nls-report-without-connections
   (implies (not (consp pins))
            (equal (fn-nls-report kind profile s bytes seen cfg pins obs fn-arena)
                   (fn-nls-report kind profile s bytes seen cfg nil obs fn-arena)))
   :hints (("Goal" :expand ((fn-nls-connection-lines pins)
                            (fn-nls-connection-lines nil))
            :in-theory '(fn-nls-report fn-nls-pins-line len)))))

;; PKT-885: the view OC carries is CURRENT when it is the view of every
;; record the Store holds: no batch is in flight, so no reader view is held
;; and the working view is the durable one.
(defun fn-nls-view-currentp (oc)
  (declare (xargs :guard t))
  (let ((o (fn-ocfg-owner oc)))
    (and (equal (fn-own-view-version (fn-own-view o))
                (len (fn-sf-records (fn-sn-files (fn-own-store o)))))
         (equal (fn-own-view-raw (fn-own-view o))
                (fn-state-articles (fn-node-acceptance
                                    (fn-sn-node (fn-own-store o))))))))

(local
 (defthm fn-nls-view-seen-of-current
   (implies (fn-nls-view-currentp oc)
            (equal (fn-nls-view-seen (fn-own-view (fn-ocfg-owner oc)))
                   (fn-nls-store-seen (fn-own-store (fn-ocfg-owner oc)))))
   :hints (("Goal" :in-theory '(fn-nls-view-currentp fn-nls-view-seen
                                fn-nls-store-seen fn-sbud-used nfix
                                (:t len))))))

(defthm fn-nls-live-report-is-the-offline-report
  (implies (and (fn-sbud-octets-cache-validp
                 cache (fn-sf-records (fn-sn-files (fn-own-store (fn-ocfg-owner oc)))))
                (not (consp (fn-ocfg-pins oc)))
                (fn-nls-view-currentp oc))
           (equal (fn-nls-live-report kind profile oc cache obs fn-arena)
                  (fn-nls-offline-report kind profile
                                         (fn-own-store (fn-ocfg-owner oc))
                                         (fn-ocfg-config oc) obs fn-arena)))
  :hints (("Goal"
           :use ((:instance fn-sbud-bytes-used-is-kernel-sum
                            (s (fn-own-store (fn-ocfg-owner oc))))
                 (:instance fn-nls-report-without-connections
                            (s (fn-own-store (fn-ocfg-owner oc)))
                            (bytes (fn-sbud-bytes-used (fn-own-store (fn-ocfg-owner oc))))
                            (seen (fn-nls-store-seen (fn-own-store (fn-ocfg-owner oc))))
                            (cfg (fn-ocfg-config oc))
                            (pins (fn-ocfg-pins oc)))
                 fn-nls-view-seen-of-current)
           :in-theory '(fn-nls-live-report fn-nls-offline-report))))

; KEYSTONE (qual-e747dbcc A3: `control list' printed no grant).  The kind
; the host hands the status path for an accepted configuration query is
; ACL2's (`fn-native-admin-result-report-kind'; host/native/operator.lisp
; fnn-operator-execute-admin passes it to fnn-operator-status-once, whose
; live arm is `fn-nls-live-report' and offline arm `fn-nls-offline-report'),
; and the report of that kind is the plan's own query report over the same
; configuration: for `control list' the rendered authority rows
; (`fn-cfg-authorities', the eighth slot), for `peer list' the peers.  The
; host no longer names a report kind for a query.
; PRF-164: `account list' is the third query kind; its report is
; books/accounts.lisp's, which books/native-admin.lisp does not include (D26),
; so the query report of all three kinds is named here.
(defun fn-nls-query-report (plan value)
  (declare (xargs :guard t))
  (cond ((equal (fn-native-admin-result-kind plan) :list-accounts)
         (fn-acct-kinds-list-report value))
        ((equal (fn-native-admin-result-kind plan) :list-consumers)
         (fn-acct-consumers-list-report value))
        (t (fn-native-admin-query-report plan value))))

(defthm fn-nls-report-of-query-kind-is-query-report
  (equal (fn-nls-report (fn-native-admin-result-report-kind plan)
                        profile s bytes seen cfg pins obs fn-arena)
         (fn-nls-query-report plan (fn-cfg-value cfg)))
  :hints (("Goal" :in-theory '(fn-nls-report fn-native-admin-result-report-kind
                               fn-native-admin-query-report
                               fn-nls-query-report))))

; -----------------------------------------------------------------------------
; The exchange: FNLS frames on the owner's control socket
;
; Request: uint KIND-CODE, uint OFFSET.  Reply: uint STATUS-CODE, uint TOTAL
; (the report's length), bytes DIGEST (the frame trailer over the whole
; report), bytes CHUNK (at most `*fn-nls-chunk-octets*' of the report from
; OFFSET).  The chunk width bounds the owner's reply and the client's read per
; request; it bounds no report: a longer report takes more requests.

(defconst *fn-nls-magic* '(70 78 76 83)) ; FNLS
(defconst *fn-nls-version* 1)
(defconst *fn-nls-request-kind* 1)
(defconst *fn-nls-reply-kind* 2)
; Work bound: report octets per reply.
(defconst *fn-nls-chunk-octets* 131072)
; Work bound: the pages of one report a client re-asks after the report
; changed under it before it answers uncertain.
(defconst *fn-nls-max-restarts* 8)
; Work bound: the reply payload's heads (two uints, two byte-string heads,
; the digest) past the chunk.
(defconst *fn-nls-max-payload* (+ *fn-nls-chunk-octets* 64))
(defconst *fn-nls-max-frame* (+ *fn-frame-overhead-octets* *fn-nls-max-payload*))

(defun fn-nls-kind-code (kind)
  (declare (xargs :guard t))
  (cond ((equal kind :status) 1) ((equal kind :pins) 2)
        ((equal kind :peers) 3) ((equal kind :obligations) 4)
        ((equal kind :control) 5) ((equal kind :health) 6)
        ((equal kind :accounts) 7)
        ; 12: past the frame-kind-3 codes (books/control-evidence.lisp
        ; fn-cev-kind-code 8..11), so no code names two reports.
        ((equal kind :consumers) 12) (t 0)))

(defun fn-nls-code-kind (code)
  (declare (xargs :guard t))
  (cond ((equal code 1) :status) ((equal code 2) :pins)
        ((equal code 3) :peers) ((equal code 4) :obligations)
        ((equal code 5) :control) ((equal code 6) :health)
        ((equal code 7) :accounts) ((equal code 12) :consumers) (t nil)))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(defun fn-nls-seal (kind payload)
  (declare (xargs :guard t))
  (if (not (and (fn-cbor-octetp kind)
                (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nls-max-payload*)))
      :bad
    (let ((protected (fn-frame-protected *fn-nls-magic* *fn-nls-version*
                                         kind payload)))
      (append protected (fn-frame-trailer protected)))))
(local (in-theory (disable (tau-system))))

(defun fn-nls-open (octets expected-kind)
  (declare (xargs :guard t))
  (if (not (fn-cbor-octet-listp octets))
      (fn-frame-error :malformed)
    (let ((opened (fn-frame-decode octets
                                   (fn-frame-trailer
                                    (fn-frame-protected-prefix octets))
                                   *fn-nls-max-payload*)))
      (if (and (fn-frame-result-okp opened)
               (equal (fn-frame-result-magic opened) *fn-nls-magic*)
               (equal (fn-frame-result-version opened) *fn-nls-version*)
               (equal (fn-frame-result-kind opened) expected-kind))
          opened
        (fn-frame-error :live-status-frame)))))

(defun fn-nls-request-encode (kind offset)
  (declare (xargs :guard t))
  (if (not (and (member-equal kind *fn-nls-kinds*) (fn-record-uint32p offset)))
      :bad
    (fn-nls-seal *fn-nls-request-kind*
                 (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                         (fn-cbor-encode (cons :uint offset))))))

; The payload grammar over an opened frame; the decode below is the open
; (fn-nls-open) followed by it, and books/native-live-buffer.lisp opens the
; frame in place and calls the grammar.
(defun fn-nls-request-payload-decode (opened)
  "(:live-status KIND OFFSET), or (:refused REASON)."
  (declare (xargs :guard t :verify-guards nil))
    (if (not (fn-frame-result-okp opened))
        (list :refused :frame)
      (let* ((payload (fn-frame-result-payload opened))
             (first (fn-record-read-uint payload)))
        (if (not (fn-record-parse-okp first))
            (list :refused :kind)
          (let ((second (fn-record-read-uint (fn-record-parse-rest first))))
            (if (not (and (fn-record-parse-okp second)
                          (fn-nls-code-kind (fn-record-parse-value first))
                          (natp (fn-record-parse-value second))
                          (null (fn-record-parse-rest second))))
                (list :refused :fields)
              (list :live-status (fn-nls-code-kind (fn-record-parse-value first))
                    (fn-record-parse-value second))))))))

(defun fn-nls-request-decode (octets)
  "(:live-status KIND OFFSET), or (:refused REASON)."
  (declare (xargs :guard t :verify-guards nil))
  (fn-nls-request-payload-decode (fn-nls-open octets *fn-nls-request-kind*)))

(defun fn-nls-status-code (status)
  (declare (xargs :guard t))
  (if (equal status :accepted) 1 2))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(defun fn-nls-reply-payload (status total digest chunk)
  (declare (xargs :guard t))
  (append (fn-cbor-encode (cons :uint (fn-nls-status-code status)))
          (fn-cbor-encode (cons :uint total))
          (fn-record-item-encode (cons :bytes digest))
          (fn-record-item-encode (cons :bytes chunk))))
(local (in-theory (disable (tau-system))))

(defun fn-nls-reply-encode (status total digest chunk)
  (declare (xargs :guard t))
  (fn-nls-seal *fn-nls-reply-kind*
               (fn-nls-reply-payload status total digest chunk)))

(defun fn-nls-reply-decode (octets)
  "(:reply STATUS TOTAL DIGEST CHUNK), or :bad."
  (declare (xargs :guard t :verify-guards nil))
  (let ((opened (fn-nls-open octets *fn-nls-reply-kind*)))
    (if (not (fn-frame-result-okp opened))
        :bad
      (let* ((r1 (fn-record-read-uint (fn-frame-result-payload opened)))
             (r2 (fn-record-read-uint (fn-record-parse-rest r1)))
             (r3 (fn-record-read-bytes (fn-record-parse-rest r2)))
             (r4 (fn-record-read-bytes (fn-record-parse-rest r3))))
        (if (not (and (fn-record-parse-okp r1) (fn-record-parse-okp r2)
                      (fn-record-parse-okp r3) (fn-record-parse-okp r4)
                      (null (fn-record-parse-rest r4))))
            :bad
          (list :reply
                (if (equal (fn-record-parse-value r1) 1) :accepted :refused)
                (fn-record-parse-value r2)
                (fn-record-parse-value r3)
                (fn-record-parse-value r4)))))))

(defun fn-nls-page-width (report offset)
  (declare (xargs :guard t))
  (min *fn-nls-chunk-octets* (nfix (- (len report) (nfix offset)))))

; A report whose length the reply's u32 total cannot carry is refused BY
; NAME (control-reply-fit, PRF-178): the refused reply's chunk, empty for
; every other refusal, carries the word below, and `fn-nls-client-step'
; reads it back as (:refused :report-past-the-total-width).  No layout
; changes: status 2, total 0, no digest, and a byte-string chunk are what
; every refused reply already framed; a client before this reads :refused.
; The report's size grows with retained state (pins, peers, obligations,
; grant rows, each up to its profile count), and it is rendered whole before
; this decision: bounding that render is packet PKT-470's, not this word's.
(defconst *fn-nls-refusal-past-the-total-width*
  (fn-record-string-octets "report-past-the-total-width"))

(defun fn-nls-reply (report offset)
  "The owner's page of REPORT from OFFSET."
  (declare (xargs :guard t :verify-guards nil))
  (cond ((and (fn-cbor-octet-listp report)
              (fn-record-uint32p (len report))
              (natp offset)
              (<= offset (len report)))
         (fn-nls-reply-encode :accepted (len report) (fn-frame-trailer report)
                              (take (fn-nls-page-width report offset)
                                    (nthcdr offset report))))
        ((and (fn-cbor-octet-listp report)
              (not (fn-record-uint32p (len report))))
         (fn-nls-reply-encode :refused 0 nil
                              *fn-nls-refusal-past-the-total-width*))
        (t (fn-nls-reply-encode :refused 0 nil nil))))

; The concrete twin of the owner's pages (D27, PKT-145).  The owner renders
; a report once per request and keeps it as a string with its frame digest
; (`fn-nls-buffer'); each page of that request is a substring of the buffer
; (`fn-nls-page'), so a page costs its chunk, not a render and a SHA-256 of
; the whole report.  `fn-nls-page-of-buffer-is-reply' equates it to the
; octet-list page `fn-nls-reply', whatever the report.  The renderer itself
; still builds octet lists; its twin is open.
; PRF-336: the report's string, built by a loop.  `fn-record-octets-string'
; conses its characters by non-tail recursion, one frame per octet: on the
; owner's 1,024 KB control stack a report past about 50,000 octets exhausted
; it and stopped the owner (`operator CONFIG obligations' at about 1,029
; obligations, the openbsd-rehearsal record of 2026-09-27, stop 2).
; `fn-nls-octets-string' is its twin with constant stack, and
; `fn-nls-octets-string-is-record-octets-string' is the equation.  Since
; PKT-693 (lane thread-stacks) `fn-record-octets-string' itself executes by a
; loop (books/records-shape.lisp, an `mbe' in `fn-record-octets-chars'), so
; `fn-nls-buffer' calls it directly; the twin and its equation stay as the
; record of the fix and for their tests.
(defun fn-nls-octets-chars-rev (octets acc)
  (declare (xargs :guard (and (fn-cbor-octet-listp octets) (character-listp acc))))
  (if (consp octets)
      (fn-nls-octets-chars-rev (cdr octets) (cons (code-char (car octets)) acc))
    acc))

(local
 (defthm fn-nls-octets-chars-rev-is-revappend
   (equal (fn-nls-octets-chars-rev octets acc)
          (revappend (fn-record-octets-chars octets) acc))))

(local
 (defthm fn-nls-revappend-revappend
   (equal (revappend (revappend x y) z)
          (revappend y (append x z)))))

(local
 (defthm fn-nls-true-listp-of-octets-chars
   (true-listp (fn-record-octets-chars octets))))

(local
 (defthm fn-nls-append-nil-when-true-listp
   (implies (true-listp x) (equal (append x nil) x))))

(local
 (defthm fn-nls-character-listp-of-revappend
   (implies (and (character-listp x) (character-listp y))
            (character-listp (revappend x y)))))

(local
 (defthm fn-nls-character-listp-of-octets-chars
   (character-listp (fn-record-octets-chars octets))))

(defun fn-nls-octets-string (octets)
  (declare (xargs :guard t))
  (if (fn-cbor-octet-listp octets)
      (coerce (reverse (fn-nls-octets-chars-rev octets nil)) 'string)
    ""))

(defthm fn-nls-octets-string-is-record-octets-string
  (equal (fn-nls-octets-string octets)
         (fn-record-octets-string octets))
  :hints (("Goal" :in-theory (enable fn-record-octets-string))))

(defun fn-nls-buffer (report)
  "(TEXT . DIGEST): REPORT as one string and the frame trailer over it, or
:bad for a report that is not octets."
  (declare (xargs :guard t :verify-guards nil))
  (if (fn-cbor-octet-listp report)
      (cons (fn-record-octets-string report) (fn-frame-trailer report))
    :bad))

(defun fn-nls-page (buffer offset)
  "The owner's page of the buffered report from OFFSET."
  (declare (xargs :guard t :verify-guards nil))
  (if (and (consp buffer)
           (stringp (car buffer))
           (fn-record-uint32p (length (car buffer)))
           (natp offset)
           (<= offset (length (car buffer))))
      (let ((text (car buffer)))
        (fn-nls-reply-encode
         :accepted (length text) (cdr buffer)
         (fn-record-string-octets
          (subseq text offset
                  (+ offset (min *fn-nls-chunk-octets* (- (length text) offset)))))))
    (if (and (consp buffer)
             (stringp (car buffer))
             (not (fn-record-uint32p (length (car buffer)))))
        (fn-nls-reply-encode :refused 0 nil
                             *fn-nls-refusal-past-the-total-width*)
      (fn-nls-reply-encode :refused 0 nil nil))))

(defun fn-nls-cached-buffer (kind offset cached)
  "The buffer an earlier page of this request rendered, or nil (render anew).
CACHED is the owner's (KIND . BUFFER) list; a request from offset 0 always
renders, so a new report starts from the state the owner holds then."
  (declare (xargs :guard t))
  (cond ((not (posp offset)) nil)
        ((atom cached) nil)
        ((and (consp (car cached)) (equal (car (car cached)) kind))
         (cdr (car cached)))
        (t (fn-nls-cached-buffer kind offset (cdr cached)))))

(defun fn-nls-cache-put (kind buffer cached)
  "CACHED with KIND's buffer replaced: at most one buffer per report kind."
  (declare (xargs :guard t))
  (cond ((atom cached) (list (cons kind buffer)))
        ((and (consp (car cached)) (equal (car (car cached)) kind))
         (cons (cons kind buffer) (cdr cached)))
        (t (cons (car cached) (fn-nls-cache-put kind buffer (cdr cached))))))

(defun fn-nls-client-step (acc total digest reply)
  "The client's word on one page, with ACC the report octets so far and
TOTAL and DIGEST the first page's: (:done REPORT), (:next ACC TOTAL DIGEST)
to ask from (len ACC), (:restart) when the report changed under the pages,
(:refused) when the owner refused, (:refused :report-past-the-total-width)
when it refused a report the u32 total cannot carry, (:transport) for a
malformed page."
  (declare (xargs :guard t :verify-guards nil))
  (let ((d (fn-nls-reply-decode reply)))
    (cond
     ((not (and (consp d) (equal (car d) :reply))) (list :transport))
     ((not (equal (nth 1 d) :accepted))
      (if (equal (nth 4 d) *fn-nls-refusal-past-the-total-width*)
          (list :refused :report-past-the-total-width)
        (list :refused)))
     ((and (consp acc)
           (not (and (equal (nth 2 d) total) (equal (nth 3 d) digest))))
      (list :restart))
     (t (let ((next (append (true-list-fix acc) (nth 4 d))))
          (cond ((not (natp (nth 2 d))) (list :transport))
                ((< (nth 2 d) (len next)) (list :transport))
                ((equal (len next) (nth 2 d)) (list :done next))
                ((not (consp (nth 4 d))) (list :transport))
                (t (list :next next (nth 2 d) (nth 3 d)))))))))

; Which process answers.  The client asks the owner whose control socket the
; configuration names; an owner that is not there (no socket, or a socket
; nothing accepts on: the connection failed before anything was sent) leaves
; the offline command, whose shared lock refuses while any owner holds the
; Store.  Any other outcome is the owner's, or uncertain, and is reported as
; such: a status is never answered from the Store behind a live owner.
(defun fn-nls-route (socket-present outcome)
  (declare (xargs :guard t))
  (cond ((not socket-present) :offline)
        ((equal outcome :before-submission) :offline)
        ((equal outcome :refused) :refused)
        (t :uncertain)))

; -----------------------------------------------------------------------------
; The exchange, proved

(encapsulate ()
(local
 (defthm fn-nls-protected-is-octets
   (implies (and (fn-frame-magicp magic)
                 (fn-cbor-octetp version)
                 (fn-cbor-octetp kind)
                 (fn-cbor-octet-listp payload)
                 (<= (len payload) *fn-cbor-max-uint*))
            (fn-cbor-octet-listp (fn-frame-protected magic version kind payload)))
   :hints (("Goal" :in-theory (e/d (fn-frame-protected fn-frame-header-octets)
                                   (fn-frame-header))))))
(local
 (defthm fn-nls-digest-is-octets
   (implies (fn-frame-digestp d) (fn-cbor-octet-listp d))
   :hints (("Goal" :in-theory (enable fn-frame-digestp)))))
(defthm fn-nls-open-of-seal
  (implies (and (fn-cbor-octetp kind)
                (fn-cbor-octet-listp payload)
                (<= (len payload) *fn-nls-max-payload*))
           (equal (fn-nls-open (fn-nls-seal kind payload) kind)
                  (fn-frame-ok *fn-nls-magic* *fn-nls-version* kind payload)))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-frame-decode-of-host-framing
                            (magic *fn-nls-magic*) (version *fn-nls-version*)
                            (max-payload *fn-nls-max-payload*))
                 (:instance fn-frame-trailer-is-a-digest
                            (octets (fn-frame-protected *fn-nls-magic* *fn-nls-version*
                                                        kind payload))))
           :in-theory (e/d (fn-nls-open fn-nls-seal fn-frame-inputp fn-frame-magicp
                            fn-frame-result-okp fn-frame-ok fn-frame-result-magic fn-frame-result-version fn-frame-result-kind)
                           (fn-frame-decode-of-host-framing fn-frame-decode
                            fn-frame-trailer-is-a-digest
                            fn-frame-protected fn-frame-trailer
                            fn-frame-protected-prefix))))))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(encapsulate ()
(local
 (defthm fn-nls-octets-of-append
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))))
(local
 (defthm fn-nls-read-bytes-alone
   (implies (and (fn-cbor-octet-listp xs) (<= (len xs) *fn-record-max-octets*))
            (equal (fn-record-read-bytes (fn-record-item-encode (cons :bytes xs)))
                   (fn-record-parse-ok xs nil)))
   :hints (("Goal" :use ((:instance fn-record-read-bytes-of-item-encoding (rest nil))
                         (:instance fn-record-item-encode-true-list (value (cons :bytes xs))))
            :in-theory (disable fn-record-read-bytes-of-item-encoding fn-record-item-encode-true-list
                                fn-record-read-bytes fn-record-item-encode)))))
(local
 (defthm fn-nls-reply-payload-octets
   (fn-cbor-octet-listp (fn-nls-reply-payload status total digest chunk))
   :hints (("Goal" :in-theory (e/d (fn-nls-reply-payload) (fn-cbor-encode fn-record-item-encode (:e fn-cbor-encode)))))))
(local
 (defthm fn-nls-open-of-reply-encode
   (implies (<= (len (fn-nls-reply-payload status total digest chunk))
                *fn-nls-max-payload*)
            (equal (fn-nls-open (fn-nls-reply-encode status total digest chunk) 2)
                   (fn-frame-ok *fn-nls-magic* *fn-nls-version* 2
                                (fn-nls-reply-payload status total digest chunk))))
   :hints (("Goal" :use ((:instance fn-nls-open-of-seal
                                    (kind 2)
                                    (payload (fn-nls-reply-payload status total digest chunk))))
            :in-theory (e/d (fn-nls-reply-encode)
                            (fn-nls-open-of-seal fn-nls-reply-payload fn-nls-open fn-nls-seal))))))
; The client reads back the status, total, digest and chunk the owner framed.
(defthm fn-nls-reply-decode-of-encode
  (implies (and (fn-record-uint32p total)
                (fn-cbor-octet-listp digest)
                (fn-cbor-octet-listp chunk)
                (<= (len digest) *fn-record-max-octets*)
                (<= (len chunk) *fn-record-max-octets*)
                (<= (len (fn-nls-reply-payload status total digest chunk))
                    *fn-nls-max-payload*))
           (equal (fn-nls-reply-decode (fn-nls-reply-encode status total digest chunk))
                  (list :reply (if (equal status :accepted) :accepted :refused)
                        total digest chunk)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nls-reply-decode fn-nls-reply-payload fn-nls-status-code
                            fn-record-read-uint-of-encoding fn-record-read-bytes-of-item-encoding fn-nls-octets-of-append fn-nls-read-bytes-alone fn-record-cbor-encode-octets fn-record-item-encode-octets
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload)
                           (fn-nls-reply-encode fn-nls-open fn-nls-seal fn-record-read-uint
                            fn-record-read-bytes (:e fn-cbor-encode)
                            fn-cbor-encode fn-record-item-encode))))))
(local (in-theory (disable (tau-system))))

(encapsulate ()
(local
 (defthm fn-nls-argument-length
   (<= (len (fn-cbor-encode-argument major n)) 5)
   :rule-classes :linear
   :hints (("Goal" :in-theory (enable fn-cbor-encode-argument fn-cbor-u16-bytes fn-cbor-u32-bytes)))))
(defthm fn-nls-bytes-item-length
  (<= (len (fn-record-item-encode (cons :bytes xs))) (+ 5 (len xs)))
  :rule-classes :linear
  :hints (("Goal" :in-theory (enable fn-record-item-encode fn-cbor-encode-bounded)))))

(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(encapsulate ()
(local
 (defthm fn-nls-octets-of-append-r
   (implies (and (fn-cbor-octet-listp a) (fn-cbor-octet-listp b))
            (fn-cbor-octet-listp (append a b)))))
(local
 (defthm fn-nls-octets-true-listp
   (implies (fn-cbor-octet-listp r) (true-listp r))))
(local
 (defthm fn-nls-read-uint-alone
   (implies (fn-record-uint32p n)
            (equal (fn-record-read-uint (fn-cbor-encode (cons :uint n)))
                   (fn-record-parse-ok n nil)))
   :hints (("Goal" :use ((:instance fn-record-read-uint-of-encoding (rest nil))
                         (:instance fn-record-cbor-encode-octets (value (cons :uint n))))
            :in-theory (disable fn-record-cbor-encode-octets fn-record-read-uint-of-encoding fn-record-read-uint fn-cbor-encode)))))
(local
 (defthm fn-nls-len-append-r
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-nls-open-of-request-encode
   (implies (and (member-equal kind *fn-nls-kinds*) (fn-record-uint32p offset))
            (equal (fn-nls-open (fn-nls-request-encode kind offset) 1)
                   (fn-frame-ok *fn-nls-magic* *fn-nls-version* 1
                                (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                                        (fn-cbor-encode (cons :uint offset))))))
   :hints (("Goal" :use ((:instance fn-nls-open-of-seal
                                    (kind 1)
                                    (payload (append (fn-cbor-encode (cons :uint (fn-nls-kind-code kind)))
                                                     (fn-cbor-encode (cons :uint offset))))))
            :in-theory (e/d (fn-nls-request-encode fn-record-cbor-encode-octets
                             fn-record-cbor-uint-encoding-bound)
                            (fn-nls-open-of-seal fn-nls-open fn-nls-seal fn-nls-kind-code
                             fn-cbor-encode (:e fn-cbor-encode)))))))
; The owner reads back the kind and offset the client framed.
(defthm fn-nls-request-decode-of-encode
  (implies (and (member-equal kind *fn-nls-kinds*) (fn-record-uint32p offset))
           (equal (fn-nls-request-decode (fn-nls-request-encode kind offset))
                  (list :live-status kind offset)))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nls-request-decode fn-nls-kind-code
                            fn-nls-code-kind fn-record-read-uint-of-encoding fn-nls-read-uint-alone
                            fn-record-cbor-encode-octets
                            fn-frame-result-okp fn-frame-ok fn-frame-result-payload)
                           (fn-nls-request-encode fn-nls-open fn-nls-seal fn-record-read-uint
                            fn-cbor-encode (:e fn-cbor-encode)))))))
(local (in-theory (disable (tau-system))))

(encapsulate ()
(local
 (defthm fn-nls-take-append-nthcdr
   (implies (and (natp off) (natp k) (<= (+ off k) (len r)))
            (equal (append (take off r) (take k (nthcdr off r)))
                   (take (+ off k) r)))
   :hints (("Goal" :induct (nthcdr off r) :in-theory (enable take nthcdr)))))
(local
 (defthm fn-nls-take-len
   (implies (true-listp r) (equal (take (len r) r) r))))
(local
 (defthm fn-nls-octet-list-true
   (implies (fn-cbor-octet-listp r) (true-listp r))
   :rule-classes :forward-chaining))
(local
 (defthm fn-nls-octets-of-take-nthcdr
   (implies (and (fn-cbor-octet-listp r) (natp off) (natp k) (<= (+ off k) (len r)))
            (fn-cbor-octet-listp (take k (nthcdr off r))))
   :hints (("Goal" :induct (nthcdr off r) :in-theory (enable take nthcdr)))))
(local
 (defthm fn-nls-trailer-octets
   (implies (fn-cbor-octet-listp r)
            (and (fn-cbor-octet-listp (fn-frame-trailer r))
                 (equal (len (fn-frame-trailer r)) 32)))
   :hints (("Goal" :use fn-frame-trailer-is-a-digest
            :in-theory (e/d (fn-frame-digestp) (fn-frame-trailer-is-a-digest fn-frame-trailer))))))
(local
 (defthm fn-nls-len-append
   (equal (len (append a b)) (+ (len a) (len b)))))
(local
 (defthm fn-nls-digest-octets
   (and (fn-cbor-octet-listp (fn-frame-digest r))
        (equal (len (fn-frame-digest r)) 32))
   :hints (("Goal" :use fn-frame-digestp-of-fn-frame-digest
            :in-theory (e/d (fn-frame-digestp) (fn-frame-digestp-of-fn-frame-digest))))))
(local
 (defthm fn-nls-len-take
   (implies (natp k) (equal (len (take k r)) k))))
(defthm fn-nls-reply-decode-of-reply
  (implies (and (fn-cbor-octet-listp report)
                (fn-record-uint32p (len report))
                (natp off) (<= off (len report)))
           (equal (fn-nls-reply-decode (fn-nls-reply report off))
                  (list :reply :accepted (len report) (fn-frame-trailer report)
                        (take (fn-nls-page-width report off) (nthcdr off report)))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-nls-reply-decode-of-encode
                            (status :accepted) (total (len report))
                            (digest (fn-frame-trailer report))
                            (chunk (take (fn-nls-page-width report off) (nthcdr off report)))))
           :in-theory (e/d (fn-nls-reply fn-nls-page-width fn-nls-reply-payload
                            fn-record-cbor-uint-encoding-bound fn-nls-bytes-item-length
                            fn-frame-trailer)
                           (fn-nls-reply-decode-of-encode fn-nls-reply-encode
                            fn-nls-reply-decode take nthcdr fn-cbor-encode
                            fn-record-item-encode)))))
(local
 (defthm fn-nls-consp-take
   (implies (posp k) (consp (take k r)))
   :hints (("Goal" :use ((:instance fn-nls-len-take))
            :in-theory (disable take fn-nls-len-take)))))
(local
 (defthm fn-nls-nthcdr-0 (equal (nthcdr 0 r) r)))
(local
 (defthm fn-nls-take-0 (equal (take 0 r) nil)))
; KEYSTONE (the pages join to the report).  The subjects are
; `fn-nls-reply', which the owner's buffered page equals
; (`fn-nls-page-of-buffer-is-reply'; host/native-live-status-host.lisp
; `fn-native-live-status-host-answer'), and
; `fn-nls-client-step', which the client folds every page through
; (host/native/control.lisp `fnn-control-live-status').  When the client
; holds a prefix ACC of an octet REPORT (and, past the first page, the
; report's total and digest), the owner's page from (len ACC) takes it to
; the whole report, or to the strictly longer prefix of one more chunk; so
; asking from (len ACC) until :done yields exactly REPORT.
(defthm fn-nls-client-step-of-owner-reply
  (implies (and (fn-cbor-octet-listp report)
                (fn-record-uint32p (len report))
                (<= (len acc) (len report))
                (equal acc (take (len acc) report))
                (or (not (consp acc))
                    (and (equal total (len report))
                         (equal digest (fn-frame-trailer report)))))
           (equal (fn-nls-client-step acc total digest (fn-nls-reply report (len acc)))
                  (if (<= (len report) (+ (len acc) *fn-nls-chunk-octets*))
                      (list :done report)
                    (list :next (take (+ (len acc) *fn-nls-chunk-octets*) report)
                          (len report) (fn-frame-trailer report)))))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nls-client-step fn-nls-page-width fn-record-uint32p)
                           (fn-nls-reply fn-nls-reply-encode fn-nls-reply-decode fn-frame-trailer
                            take nthcdr fn-cbor-encode fn-record-item-encode))))))

; -----------------------------------------------------------------------------
; The buffered page (D27 twin, PKT-145), proved

(encapsulate ()
(local
 (defthm fn-nls-chars-len
   (equal (len (fn-record-octets-chars r)) (len r))))
(local
 (defthm fn-nls-chars-are-characters
   (character-listp (fn-record-octets-chars r))))
(local
 (defthm fn-nls-take-of-chars
   (implies (<= (nfix k) (len r))
            (equal (take k (fn-record-octets-chars r))
                   (fn-record-octets-chars (take k r))))
   :hints (("Goal" :induct (nthcdr k r) :in-theory (enable take nthcdr)))))
(local
 (defthm fn-nls-nthcdr-of-chars
   (equal (nthcdr k (fn-record-octets-chars r))
          (fn-record-octets-chars (nthcdr k r)))
   :hints (("Goal" :in-theory (enable nthcdr)))))
(local
 (defthm fn-nls-len-nthcdr
   (equal (len (nthcdr k r)) (nfix (- (len r) (nfix k))))
   :hints (("Goal" :induct (nthcdr k r) :in-theory (enable nthcdr)))))
(local
 (defthm fn-nls-plus-cancel
   (equal (+ x (+ (- x) y)) (fix y))))
(local
 (defthm fn-nls-octets-of-chars
   (implies (fn-cbor-octet-listp r)
            (equal (fn-record-string-octets-aux (fn-record-octets-chars r)) r))
   :hints (("Goal" :in-theory (enable fn-cbor-octet-listp fn-cbor-octetp)))))
(local
 (defthm fn-nls-octets-of-take-nthcdr-b
   (implies (and (fn-cbor-octet-listp r) (natp off) (natp k) (<= (+ off k) (len r)))
            (fn-cbor-octet-listp (take k (nthcdr off r))))
   :hints (("Goal" :induct (nthcdr off r) :in-theory (enable take nthcdr)))))
; The owner's buffered page is the octet-list page of the same report, for
; every report and offset.  The subject is `fn-nls-page' over
; `fn-nls-buffer', which the owner answers with
; (host/native-live-status-host.lisp `fn-native-live-status-host-answer',
; called by host/native/control.lisp `fnn-control-live-status-answer').
(defthm fn-nls-page-of-buffer-is-reply
  (equal (fn-nls-page (fn-nls-buffer report) off)
         (fn-nls-reply report off))
  :hints (("Goal" :do-not-induct t
           :in-theory (e/d (fn-nls-page fn-nls-buffer fn-nls-reply fn-nls-page-width
                            fn-record-octets-string fn-record-string-octets
                            subseq subseq-list)
                           (fn-nls-reply-encode fn-frame-trailer take nthcdr
                            fn-record-octets-chars fn-record-string-octets-aux))))))

; KEYSTONE (the pages the owner answers from its buffer join to the report).
; `fn-nls-client-step-of-owner-reply' restated over the function the owner
; calls: the client's step on the buffered page from (len ACC) is its step
; on `fn-nls-reply', which that keystone decides.
(defthm fn-nls-client-step-of-owner-page
  (implies (and (fn-cbor-octet-listp report)
                (fn-record-uint32p (len report))
                (<= (len acc) (len report))
                (equal acc (take (len acc) report))
                (or (not (consp acc))
                    (and (equal total (len report))
                         (equal digest (fn-frame-trailer report)))))
           (equal (fn-nls-client-step acc total digest
                                      (fn-nls-page (fn-nls-buffer report) (len acc)))
                  (if (<= (len report) (+ (len acc) *fn-nls-chunk-octets*))
                      (list :done report)
                    (list :next (take (+ (len acc) *fn-nls-chunk-octets*) report)
                          (len report) (fn-frame-trailer report)))))
  :hints (("Goal" :use (fn-nls-client-step-of-owner-reply
                        (:instance fn-nls-page-of-buffer-is-reply (off (len acc))))
           :in-theory nil)))

; KEYSTONE (control-reply-fit, PRF-178: the width refusal is named, exactly
; past the width).  For an octet report and ANY offset, the client's step on
; the owner's buffered page (host/native-live-status-host.lisp
; `fn-native-live-status-host-answer', called by host/native/control.lisp
; `fnn-control-live-status-answer'; the client's step through
; `fn-native-live-status-host-client-step', host/native/control.lisp
; `fnn-control-live-status') is the named refusal
; (:refused :report-past-the-total-width) exactly when the report is longer
; than the reply's u32 total can say.  Within the width it is an accepted
; page (`fn-nls-client-step-of-owner-page' says which) or, for an offset
; past the report, the unnamed refusal it always was.
(local (in-theory (enable (tau-system)))) ; tau-cost: this form needs tau
(encapsulate ()
(local
 (defthm fn-nls-reply-refusals
   (implies (fn-cbor-octet-listp report)
            (and (implies (not (fn-record-uint32p (len report)))
                          (equal (fn-nls-reply report off)
                                 (fn-nls-reply-encode
                                  :refused 0 nil
                                  *fn-nls-refusal-past-the-total-width*)))
                 (implies (and (fn-record-uint32p (len report))
                               (not (and (natp off) (<= off (len report)))))
                          (equal (fn-nls-reply report off)
                                 (fn-nls-reply-encode :refused 0 nil nil)))))
   :hints (("Goal" :in-theory (e/d (fn-nls-reply)
                                   (fn-nls-reply-encode (:e fn-nls-reply-encode)))))))
(local
 (defthm fn-nls-client-step-of-the-refusals
   (and (equal (fn-nls-client-step acc total digest
                                   (fn-nls-reply-encode
                                    :refused 0 nil
                                    *fn-nls-refusal-past-the-total-width*))
               '(:refused :report-past-the-total-width))
        (equal (fn-nls-client-step acc total digest
                                   (fn-nls-reply-encode :refused 0 nil nil))
               '(:refused)))
   :hints (("Goal" :use ((:instance fn-nls-reply-decode-of-encode
                                    (status :refused) (total 0) (digest nil)
                                    (chunk *fn-nls-refusal-past-the-total-width*))
                         (:instance fn-nls-reply-decode-of-encode
                                    (status :refused) (total 0) (digest nil)
                                    (chunk nil)))
            :in-theory (e/d (fn-nls-client-step)
                            (fn-nls-reply-decode-of-encode fn-nls-reply-decode
                             fn-nls-reply-encode (:e fn-nls-reply-encode)))))))
(defthm fn-nls-page-refuses-exactly-past-the-total-width
  (implies (fn-cbor-octet-listp report)
           (equal (equal (fn-nls-client-step acc total digest
                                             (fn-nls-page (fn-nls-buffer report) off))
                         '(:refused :report-past-the-total-width))
                  (< *fn-cbor-max-uint* (len report))))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :cases ((not (fn-record-uint32p (len report)))
                   (and (fn-record-uint32p (len report))
                        (not (and (natp off) (<= off (len report)))))
                   (and (fn-record-uint32p (len report))
                        (natp off) (<= off (len report))))
           :in-theory (e/d (fn-nls-client-step)
                           (fn-nls-page fn-nls-buffer fn-nls-reply
                            fn-nls-reply-decode fn-nls-reply-encode
                            (:e fn-nls-reply-encode) fn-record-uint32p
                            fn-cbor-octet-listp
                            fn-frame-trailer take nthcdr fn-nls-page-width)))))
)
(local (in-theory (disable (tau-system))))

; Every later page of one request reads the buffer its first page rendered:
; a request from offset 0 renders and stores it, and a positive offset of
; the same kind finds it.  (`fn-nls-cached-buffer' is the owner's choice
; between the stored buffer and a fresh render.)
(defthm fn-nls-cached-buffer-of-put
  (implies (posp off)
           (equal (fn-nls-cached-buffer kind off (fn-nls-cache-put kind buffer cached))
                  buffer))
  ;; The two definitions and nothing else: under the book's default theory
  ;; this took 9 s of the book's 11 (hbox, run-20260925T191541Z-026e).
  :hints (("Goal" :induct (fn-nls-cache-put kind buffer cached)
                  :in-theory '(fn-nls-cached-buffer fn-nls-cache-put
                               car-cons cdr-cons))))

; PKT-269 (PRF-187): the retention lines the health verdict reads
; (books/native-health.lisp fn-nh-forward-pins) run guard-verified.
(verify-guards fn-nls-connection-lines-step)
(verify-guards fn-nls-connection-lines-loop)
(verify-guards fn-nls-connection-lines
  :hints (("Goal" :use ((:instance fn-nls-connection-lines-loop-of-rev-onto (zs nil))))))
(encapsulate ()
  (local
   (defthm fn-nls-revappend-revappend-lines
     (equal (revappend (revappend x y) z)
            (revappend y (append x z)))))
  (local
   (defthm fn-nls-revappend-of-append-lines
     (equal (revappend (append x y) z)
            (revappend y (revappend x z)))))
  (local
   (defthm fn-nls-obligation-lines-rev-is-revappend
     (equal (fn-nls-obligation-lines-rev pins acc)
            (revappend (fn-nls-obligation-lines pins) acc))
     :hints (("Goal" :in-theory (disable fn-nls-obligation-line)))))
  (local
   (defthm fn-nls-true-listp-of-obligation-lines
     (true-listp (fn-nls-obligation-lines pins))))
  (local
   (defthm fn-nls-append-nil-lines
     (implies (true-listp x) (equal (append x nil) x))))
  (verify-guards fn-nls-obligation-line)
  (verify-guards fn-nls-obligation-lines-rev)
  (verify-guards fn-nls-obligation-lines
    :hints (("Goal" :in-theory (disable fn-nls-obligation-line)))))
(verify-guards fn-nls-retention)
(verify-guards fn-nls-pins-line)
