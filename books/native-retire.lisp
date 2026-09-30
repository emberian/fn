; Retiring a node (row S9; operability review drag 11; M1's "drain before
; retiring"): `fn operator CONFIG retire [--drain SECONDS]'.
;
; The verb asks the running owner to retire.  From that request on the owner
; answers every new connection with the refusal below and closes it, stops
; pulling from its peers, and lets its feeds drain for at most SECONDS
; (books/owner-retire.lisp decides when the drain ends and renders what stays
; undelivered, per peer, and the obligation ledger).  Then it takes a final
; checkpoint and stops as a SIGTERM stops it (the POSTs in flight answered
; first, books/owner-stop-drain.lisp).  What cannot drain is released only by
; the waiver (`carry drop WORK --abandon', FNCC :waive, PRF-950), on the
; stopped store.
;
; This book is the operator's side: the command's decision (SECONDS within
; the bound, refused by name past it), the request vector the operator sends
; over the control socket and the owner's recognizer of it, and the line a
; new connection receives while the node retires.
(in-package "ACL2")
(include-book "records")

; The drain window's bound: one retire holds the node half-open (serving the
; sessions it has, refusing new ones) for at most this long.  A work bound on
; one command, as `status --watch''s interval (books/native-operator.lisp
; *fn-nop-max-watch-seconds*), never a bound on data: a feed that has not
; drained by then is reported and released by the waiver.
(defconst *fn-nret-max-drain-seconds* 86400)

; The command's decision.  SECONDS is the operator's --drain value as the
; grammar parsed it: a natural, or :not-a-number when the text was not a
; decimal.  Without --drain the window is 0: nothing is waited for.
;   (:accepted SECONDS) | (:refused REASON)
(defun fn-nret-plan (seconds)
  (declare (xargs :guard t))
  (cond ((not (natp seconds)) (list :refused :drain-seconds-not-a-number))
        ((< *fn-nret-max-drain-seconds* seconds)
         (list :refused :drain-seconds-over-bound))
        (t (list :accepted seconds))))

(defthm fn-nret-plan-accepts-exactly-the-bounded-window
  (equal (equal (car (fn-nret-plan seconds)) :accepted)
         (and (natp seconds) (<= seconds *fn-nret-max-drain-seconds*))))

(defthm fn-nret-plan-accepted-window
  (implies (equal (car (fn-nret-plan seconds)) :accepted)
           (equal (cadr (fn-nret-plan seconds)) seconds)))

; The request vector: ("retire" "begin" S3 S2 S1 S0), SECONDS as four
; big-endian octets (the bound is below 2^32).  The owner recognizes exactly
; these vectors (fn-nret-request), before any administrative plan.
(defun fn-nret-u32-octets (n)
  (declare (xargs :guard t))
  (let ((n (nfix n)))
    (list (mod (floor n 16777216) 256) (mod (floor n 65536) 256)
          (mod (floor n 256) 256) (mod n 256))))

(defun fn-nret-u32-value (xs)
  (declare (xargs :guard t))
  (if (and (true-listp xs) (equal (len xs) 4)
           (natp (car xs)) (< (car xs) 256)
           (natp (cadr xs)) (< (cadr xs) 256)
           (natp (caddr xs)) (< (caddr xs) 256)
           (natp (cadddr xs)) (< (cadddr xs) 256))
      (+ (* 16777216 (car xs)) (* 65536 (cadr xs)) (* 256 (caddr xs)) (cadddr xs))
    nil))

(defun fn-nret-request-argv (seconds)
  (declare (xargs :guard t))
  (list (fn-record-string-octets "retire")
        (fn-record-string-octets "begin")
        (fn-nret-u32-octets seconds)))

;   (:begin SECONDS) for a retire vector, NIL for every other vector.
(defun fn-nret-request (argv)
  (declare (xargs :guard t))
  (if (and (true-listp argv) (equal (len argv) 3)
           (equal (car argv) (fn-record-string-octets "retire"))
           (equal (cadr argv) (fn-record-string-octets "begin")))
      (let ((n (fn-nret-u32-value (caddr argv))))
        (if (and (natp n) (<= n *fn-nret-max-drain-seconds*))
            (list :begin n)
          nil))
    nil))

(local (include-book "arithmetic-5/top" :dir :system))

(local
 (defthm fn-nret-u32-value-of-octets
   (implies (and (natp n) (< n 4294967296))
            (equal (fn-nret-u32-value (fn-nret-u32-octets n)) n))))

; KEYSTONE (the owner reads the window the operator decided).  The subject is
; fn-nret-request, which host/native/admin.lisp fnn-owner-live-admin-serialized
; calls on every administrative vector; the vector is
; fn-native-operator-result-retire-argv's (books/native-operator.lisp), sent
; by host/native/operator.lisp fnn-operator-execute-retire.  Every window the
; command accepts arrives unchanged.
(defthm fn-nret-request-of-request-argv
  (implies (equal (car (fn-nret-plan seconds)) :accepted)
           (equal (fn-nret-request (fn-nret-request-argv seconds))
                  (list :begin seconds))))

; A vector that is not a retire vector is not a retire request, whatever it
; carries: the administrative plans are unchanged.
(defthm fn-nret-request-needs-the-retire-word
  (implies (not (equal (car argv) (fn-record-string-octets "retire")))
           (equal (fn-nret-request argv) nil)))

(defthm fn-nret-request-window-is-bounded
  (implies (fn-nret-request argv)
           (and (equal (car (fn-nret-request argv)) :begin)
                (natp (cadr (fn-nret-request argv)))
                (<= (cadr (fn-nret-request argv)) *fn-nret-max-drain-seconds*))))

; The owner's answer to a retire request: a node retires once.
;   (STATUS WORD) with STATUS :accepted or :refused.
(defun fn-nret-begin-answer (retiring)
  (declare (xargs :guard t))
  (if retiring
      (list :refused :already-retiring)
    (list :accepted :draining)))

; What a new connection receives while the node retires, on a plain listener:
; RFC 3977 section 5.1.1's 502 greeting (service permanently unavailable),
; then the owner closes it.  An implicit-TLS listener closes without it: a
; plaintext line is never written into a TLS port (tls-handshake-budget).
(defun fn-nret-refusal-line ()
  (declare (xargs :guard t))
  (fn-record-string-octets
   (concatenate 'string "502 this node is retiring and accepts no new connections"
                (coerce (list (code-char 13) (code-char 10)) 'string))))

; The owner's log line for a refused connection (the reason word).
(defun fn-nret-refused-log-line (tls)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (if tls
       "retire refused connection reason=retiring listener=tls"
     "retire refused connection reason=retiring listener=plain")))

; The report's file, under the store's directory: written by the owner when
; the drain ends, fenced before the stop, read by the operator from the
; stopped node (host/native/admin.lisp fnn-owner-retire-write-report).
(defun fn-nret-report-file-name ()
  (declare (xargs :guard t))
  (fn-record-string-octets "retire-report.txt"))

(defun fn-nret-digits (n acc)
  (declare (xargs :guard (natp n) :measure (nfix n)))
  (if (zp n)
      acc
    (fn-nret-digits (floor n 10) (cons (+ 48 (mod n 10)) acc))))

(defun fn-nret-decimal (n)
  (declare (xargs :guard t))
  (if (posp n) (fn-nret-digits n nil) (list 48)))

; The owner's log lines at the request and when the drain ends.
(defun fn-nret-begin-log-line (seconds)
  (declare (xargs :guard t))
  (append (fn-record-string-octets "retire begin reason=operator drain-seconds=")
          (fn-nret-decimal seconds)))

(defun fn-nret-end-log-line (step)
  (declare (xargs :guard t))
  (fn-record-string-octets
   (if (equal step :drained)
       "retire end state=drained (final checkpoint taken; stopping)"
     "retire end state=deadline (final checkpoint taken; stopping)")))

; What the operator prints when no owner runs: nothing drains a stopped node.
(defun fn-nret-not-running-line ()
  (declare (xargs :guard t))
  (fn-record-string-octets
   "retire refused reason=not-running (the node is stopped: nothing drains; `obligations' names what it holds)"))

; What the operator prints when the owner stopped without a report.
(defun fn-nret-no-report-line ()
  (declare (xargs :guard t))
  (fn-record-string-octets
   "retire uncertain reason=no-report (the node stopped without writing retire-report.txt; see its log)"))

(in-theory (disable fn-nret-plan fn-nret-request fn-nret-request-argv
                    fn-nret-u32-octets fn-nret-u32-value fn-nret-begin-answer))
