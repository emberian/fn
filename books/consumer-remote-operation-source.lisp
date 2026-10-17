; The FNCR connection class: its funding and the admission of its reads
; (D48 / PKT-673; specs/applications.md "Remote consumer").
;
; Interim tariff (planning/design/tariff-2026-10-04.md, the projection-stage
; draw of resource-syncer.lisp, HST-046): one private resource ledger for
; the class, installed once at startup with budget MAX-SESSIONS times the
; connection vector, baseline and reserve zero (slots 0 and 1), and one user
; slot per session (2 .. MAX-SESSIONS+1).  A session draws its vector at
; accept, BEFORE the TLS handshake or any read, and settles it only at
; physical close (thread joined, socket closed).  The vector, in
; *fn-rv-coordinates* order:
;   resident     the frame read bound + the poll reply bound + the session
;                thread's stack and runtime (the syncer's reading)
;   descriptors  1 (the socket)       workers  1 (the session's thread)
;   conn-ids     1 (spent)
; This is a partial fixed-storage projection, not the complete tariff: the
; owner work a request causes is the local consumer operation's, charged
; where the control socket's is.  The connection's own charge row is owed
; to the tariff packet's Q2 amendment (i), `:principal :connection'.
;
; The reads: a header read or a frame read is admitted only for a live draw
; and only within the frame bound the draw paid for.  An unfunded or stale
; connection, an unknown kind, or a larger read is refused by name before
; one octet is read.
(in-package "ACL2")
(include-book "resource-vector-exec")
(include-book "consumer-remote-codec")
(include-book "profile-limits")

; The remote profile's query is the local profile's: one group.
(defconst *fn-crf-groups* 1)
(defconst *fn-crf-max-sessions* 64)
(defun fn-crf-groups () (declare (xargs :guard t)) *fn-crf-groups*)

(defun fn-crf-frame-octets ()
  (declare (xargs :guard t))
  (fn-cr-read-bound *fn-crf-groups*))

(defun fn-crf-reply-octets ()
  (declare (xargs :guard t))
  (+ *fn-frame-overhead-octets* *fn-ncl-poll-max-payload*))

(defun fn-crf-resident (stack)
  (declare (xargs :guard t))
  (+ (fn-crf-frame-octets) (fn-crf-reply-octets) (nfix stack)
     (* 1048576 (fn-profile-limit :thread-runtime-mib))))

(defun fn-fncr-connection-vector (resident)
  (declare (xargs :guard t))
  (list (nfix resident) 0 1 1 0 0 0 1 0))

; Reusable coordinates hold MAX-SESSIONS sessions at once.  Connection
; identities are spent: their budget is the representable identity space
; (one u64 word), so the class refuses only on exhaustion of that space,
; never after MAX-SESSIONS connections in its lifetime.
(defun fn-crf-budget (sessions resident)
  (declare (xargs :guard t))
  (let ((n (nfix sessions)))
    (list (* n (nfix resident)) 0 n n 0 0 0 *fn-rl-word-max* 0)))

(defun fn-crf-install (max-sessions stack fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (let ((resident (fn-crf-resident stack)))
    (if (not (and (posp max-sessions) (<= max-sessions *fn-crf-max-sessions*)
                  (natp stack) (<= resident *fn-rl-word-max*)
                  (<= (* max-sessions resident) *fn-rl-word-max*)))
        (mv :invalid-remote-sessions fn-resource-ledger)
      (mv-let (word fn-resource-ledger)
        (fn-rl-install (fn-crf-budget max-sessions resident)
                       *fn-rv-zero* *fn-rv-zero* (+ 2 max-sessions)
                       fn-resource-ledger)
        (if (eq word :installed)
            (let ((fn-resource-ledger
                   (update-fn-rl-worker-resident resident fn-resource-ledger)))
              (mv word fn-resource-ledger))
          (mv word fn-resource-ledger))))))

; The first idle user slot at or after I, or nil.  Bounded by the slot count.
(defun fn-crf-idle-slot (i fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (natp i) (fn-rl-wfp fn-resource-ledger))
                  :measure (nfix (- (nfix (fn-rl-count fn-resource-ledger)) (nfix i)))))
  (cond ((or (not (natp i)) (>= i (nfix (fn-rl-count fn-resource-ledger)))) nil)
        ((eql (fn-rl-phasesi i fn-resource-ledger) 0) i)
        (t (fn-crf-idle-slot (+ 1 i) fn-resource-ledger))))

(defun fn-crf-tokenp (token)
  (declare (xargs :guard t))
  (and (true-listp token) (equal (len token) 3) (eq (car token) :fncr)
       (natp (nth 1 token)) (<= 2 (nth 1 token)) (natp (nth 2 token))))

; At accept: (mv :drawn TOKEN ledger) or (mv WORD nil ledger), WORD one of
; :not-installed, :sessions (every slot in use) or fn-rl-draw's refusal
; (:resources-unavailable ...), the ledger unchanged on every refusal.
(defun fn-crf-open (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (if (not (and (fn-rl-wfp fn-resource-ledger) (<= 3 (fn-rl-count fn-resource-ledger))))
      (mv :not-installed nil fn-resource-ledger)
    (let ((slot (fn-crf-idle-slot 2 fn-resource-ledger)))
      (if (not slot)
          (mv :sessions nil fn-resource-ledger)
        (mv-let (word gen fn-resource-ledger)
          (fn-rl-draw slot (fn-fncr-connection-vector
                            (fn-rl-worker-resident fn-resource-ledger))
                      fn-resource-ledger)
          (if (eq word :drawn)
              (mv :drawn (list :fncr slot gen) fn-resource-ledger)
            (mv word nil fn-resource-ledger)))))))

(defun fn-crf-livep (token fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (and (fn-crf-tokenp token) (fn-rl-wfp fn-resource-ledger)
       (< (nth 1 token) (fn-rl-count fn-resource-ledger))
       (eql (fn-rl-phasesi (nth 1 token) fn-resource-ledger) 1)
       (equal (fn-rl-gensi (nth 1 token) fn-resource-ledger) (nth 2 token))))

; At PHYSICAL close only: the session's thread has ended and its socket is
; closed.  A stale token settles nothing.
(defun fn-crf-close (token fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (if (not (fn-crf-livep token fn-resource-ledger))
      (mv :stale fn-resource-ledger)
    (fn-rl-settle (nth 1 token) (nth 2 token) fn-resource-ledger)))

; The first user slot at or after I still drawn, or nil.
(defun fn-crf-busy-slot (i fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :verify-guards nil
                  :guard (and (natp i) (fn-rl-wfp fn-resource-ledger))
                  :measure (nfix (- (nfix (fn-rl-count fn-resource-ledger)) (nfix i)))))
  (cond ((or (not (natp i)) (>= i (nfix (fn-rl-count fn-resource-ledger)))) nil)
        ((not (eql (fn-rl-phasesi i fn-resource-ledger) 0)) i)
        (t (fn-crf-busy-slot (+ 1 i) fn-resource-ledger))))

; Every session has settled (the stop's final observation).
(defun fn-crf-drainedp (fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (and (fn-rl-wfp fn-resource-ledger)
       (not (fn-crf-busy-slot 2 fn-resource-ledger))))

; The admission of one read on a funded connection.
(defun fn-cro-read-plan (kind count livep)
  (declare (xargs :guard t))
  (cond ((not (member-eq kind '(:remote-header :remote-frame)))
         '(:refused :remote-operation-kind))
        ((not livep) '(:refused :remote-connection-unfunded))
        ((not (natp count)) '(:refused :remote-frame-size))
        ((eq kind :remote-header)
         (if (equal count *fn-frame-header-octets*) '(:admitted)
           '(:refused :remote-frame-size)))
        ((<= count (- (fn-crf-frame-octets) *fn-frame-header-octets*)) '(:admitted))
        (t '(:refused :remote-frame-size))))

(defun fn-owner-remote-operation-preflight (kind count token fn-resource-ledger)
  (declare (xargs :stobjs fn-resource-ledger :guard t :verify-guards nil))
  (fn-cro-read-plan kind count (fn-crf-livep token fn-resource-ledger)))

; The host-called entries have verified stobj guards (host/interfaces.lisp
; declares them :common-lisp-compliant).
(verify-guards fn-crf-idle-slot :hints (("Goal" :in-theory (enable fn-rl-wfp))))
(verify-guards fn-crf-busy-slot :hints (("Goal" :in-theory (enable fn-rl-wfp))))
(verify-guards fn-crf-install
  :hints (("Goal" :in-theory (disable fn-rl-install fn-crf-resident fn-crf-budget))))
(verify-guards fn-crf-open :hints (("Goal" :in-theory (enable fn-rl-wfp fn-rl-slotp))))
(verify-guards fn-crf-livep :hints (("Goal" :in-theory (enable fn-rl-wfp fn-crf-tokenp))))
(verify-guards fn-crf-close :hints (("Goal" :in-theory (enable fn-rl-wfp fn-crf-tokenp))))
(verify-guards fn-crf-drainedp)
(verify-guards fn-owner-remote-operation-preflight)

; What an admitted read is: a live draw's, and within the frame bound that
; draw's resident coordinate paid for.
(defthm fn-cro-admitted-read-is-funded-and-bounded
  (implies (equal (fn-owner-remote-operation-preflight kind count token fn-resource-ledger)
                  '(:admitted))
           (and (fn-crf-livep token fn-resource-ledger)
                (member-eq kind '(:remote-header :remote-frame))
                (natp count)
                (<= count (fn-crf-frame-octets))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-owner-remote-operation-preflight fn-cro-read-plan)
                                  (fn-crf-livep fn-crf-frame-octets)))))

; The draw pays for the frame: its resident coordinate covers the read bound.
(defthm fn-crf-resident-covers-the-frame
  (<= (fn-crf-frame-octets) (car (fn-fncr-connection-vector (fn-crf-resident stack))))
  :rule-classes nil
  :hints (("Goal" :in-theory (e/d (fn-crf-resident fn-fncr-connection-vector)
                                  (fn-crf-frame-octets)))))

(defthm fn-cro-unfunded-read-is-refused
  (implies (not (fn-crf-livep token fn-resource-ledger))
           (not (equal (fn-owner-remote-operation-preflight kind count token fn-resource-ledger)
                       '(:admitted))))
  :hints (("Goal" :in-theory (e/d (fn-owner-remote-operation-preflight fn-cro-read-plan)
                                  (fn-crf-livep)))))

(in-theory (disable fn-cro-read-plan fn-owner-remote-operation-preflight))
