; A5r's refinement keystone at the host boundary (layer doc 4.1.6): a legal
; native schedule is, at the wire, the canonical simulated one. Its sides:
; the replay of a native boundary trace through the core's own entries
; (sim/check-envelope.lisp, item 1 only: no byte comparison), and D's logical
; adapter view fn2-conn-wire-run (the subject of T1 and T8) over the clients'
; octets and Receive cuts read from the trace itself.
(in-package "ACL2")
(include-book "owed-conn")
(include-book "../sim/check-envelope")

(make-event (value (fn2-declare '(:operation-set fn2-native-boundary) nil nil nil)))

(defconst *fn2-native-profile* (put-assoc-equal :trace nil *fn2-conn-wire-profile*))

(defun fn2-envelope-steps-ok-p (trace)
  (declare (xargs :verify-guards nil))
  (eq (car (fn2-envelope-replay trace *fn2-native-profile* nil)) :pass))

; Per connection, in Accept order: the octets the replay's Sends carried.
(defun fn2-env-wires-of (caps)
  (declare (xargs :verify-guards nil))
  (if (atom caps) nil
    (cons (reverse (nth 3 (cdr (car caps)))) (fn2-env-wires-of (cdr caps)))))
(defun fn2-envelope-replay-wires (trace)
  (declare (xargs :verify-guards nil))
  (fn2-env-wires-of (cadr (fn2-envelope-replay trace *fn2-native-profile* nil))))

; Per connection, from the trace alone: (octets cuts), the Receive octets and
; their counts in order, keyed by the incarnation of the latest take of the
; posting slot. CONNS is ((key octets-newest-first cuts-newest-first) ...)
; newest connection first; KINDS maps a slot to (kind cap nonce).
(defun fn2-env-trace-conns (trace kinds conns)
  (declare (xargs :verify-guards nil :measure (len trace)))
  (if (atom trace) (reverse conns)
    (let ((e (car trace)))
      (cond
       ((and (consp e) (eq (car e) :take))
        (fn2-env-trace-conns (cdr trace) (put-assoc-equal (nth 1 e) (list (nth 3 e) (nth 4 e) (nth 5 e)) kinds) conns))
       ((and (consp e) (eq (car e) :post) (equal (nth 4 e) *fn2-event-accept-result*)
             (equal (nth 5 e) *fn2-outcome-done*))
        (fn2-env-trace-conns (cdr trace) kinds (cons (list (cons (nth 8 e) (nth 9 e)) nil nil) conns)))
       ((and (consp e) (eq (car e) :post) (equal (nth 4 e) *fn2-event-receive-result*)
             (equal (nth 5 e) *fn2-outcome-done*) (< 0 (nfix (nth 7 e))))
        (let* ((k (cdr (assoc-equal (nth 2 e) kinds))) (key (cons (nth 1 k) (nth 2 k)))
               (c (assoc-equal key conns)))
          (fn2-env-trace-conns (cdr trace) kinds
                               (if c (put-assoc-equal key (list (revappend (nth 12 e) (nth 1 c)) (cons (nth 7 e) (nth 2 c))) conns)
                                 conns))))
       (t (fn2-env-trace-conns (cdr trace) kinds conns))))))
(defun fn2-env-transcripts (conns)
  (declare (xargs :verify-guards nil))
  (if (atom conns) nil
    (cons (list (reverse (nth 1 (car conns))) (reverse (nth 2 (car conns))))
          (fn2-env-transcripts (cdr conns)))))
(defun fn2-env-cw-wires (results)
  (declare (xargs :verify-guards nil))
  (if (atom results) nil (cons (car (car results)) (fn2-env-cw-wires (cdr results)))))
(defun fn2-envelope-canonical-wires (trace)
  (declare (xargs :verify-guards nil))
  (fn2-env-cw-wires (nth 1 (fn2-conn-wire-run (fn2-env-transcripts (fn2-env-trace-conns trace nil nil))))))

; No client sent DATE (the canonical view posts no clock), case-insensitively.
(defun fn2-env-upcase (o) (declare (xargs :guard t)) (if (and (natp o) (<= 97 o) (<= o 122)) (- o 32) o))
(defun fn2-env-mentions-date-p (octets)
  (declare (xargs :verify-guards nil))
  (and (consp octets)
       (or (and (equal (fn2-env-upcase (car octets)) 68) (consp (cdr octets))
                (equal (fn2-env-upcase (cadr octets)) 65) (consp (cddr octets))
                (equal (fn2-env-upcase (caddr octets)) 84) (consp (cdddr octets))
                (equal (fn2-env-upcase (cadddr octets)) 69))
           (fn2-env-mentions-date-p (cdr octets)))))
(defun fn2-env-conns-date-free-p (transcripts)
  (declare (xargs :verify-guards nil))
  (or (atom transcripts)
      (and (not (fn2-env-mentions-date-p (car (car transcripts))))
           (fn2-env-conns-date-free-p (cdr transcripts)))))
(defun fn2-envelope-date-free-p (trace)
  (declare (xargs :verify-guards nil))
  (fn2-env-conns-date-free-p (fn2-env-transcripts (fn2-env-trace-conns trace nil nil))))

(defthm-owed fn2-native-envelope-refines (trace)
  (implies (and (fn2-envelope-steps-ok-p trace) (fn2-envelope-date-free-p trace)
                (<= (len (fn2-env-trace-conns trace nil nil)) 4))
           (equal (fn2-envelope-replay-wires trace) (fn2-envelope-canonical-wires trace)))
  :schema :invariant :from (:operation-set fn2-native-boundary)
  :teeth (fn2-native-test-refines fn2-native-test-refines-negative)
  :doc "A5r: a native adapter schedule that ENVELOPE finds legal (each take the replay's outbox head, each post an allowed, accepted completion of an acknowledged op) sends every connection, at the wire, what D's canonical adapter view fn2-conn-wire-run sends for the same client octets and Receive cuts; so T1 and T8 over the canonical view transfer to the native run. DATE is excluded (the canonical view posts no clock); at most C connections.")
