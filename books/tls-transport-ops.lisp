; Guarded decisions called by the native TLS adapter; no raw I/O here.
(in-package "ACL2")
(include-book "tls-transport-lifecycle")
(fn2-book-layer :d)
(defcodec-transport-operations fn2-tls-transport)

(defun fn2-tls-transport-start (cap nonce slot generation total capacity quantum budget window fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
                 :guard (fn2-tls-transport-wfp fn2-tls-transport)))
 ; TLS retains its explicit profile work bound; generic finite-copy codecs may need 33 bits.
 (if (not (and (unsigned-byte-p 32 budget) (posp window) (unsigned-byte-p 31 window)))
     (mv :bounds fn2-tls-transport)
  (mv-let (code fn2-tls-transport)
   (fn2-tls-transport-begin cap nonce slot generation total capacity quantum quantum window budget fn2-tls-transport)
   (if (eq code :ok)
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (ssl-status 5))))
        (mv :ok fn2-tls-transport))
     (mv code fn2-tls-transport)))))

(defun fn2-tls-transport-plan
 (total copied fed input-length input-offset output-length output-offset ssl room pending quantum)
 (declare (xargs :guard t))
 (mv-let (copy-code action offset count)
  (fn2-codec-copy-plan total copied fed input-length input-offset output-length output-offset ssl room pending quantum)
  (if (not (eq copy-code :done)) (mv copy-code action offset count)
   (cond
((< output-offset output-length) (mv :act 5 output-offset (min quantum (- output-length output-offset))))
((< 0 pending) (mv :act 4 0 (min quantum pending)))
((equal ssl 0) (mv :done 0 0 0))
((and (< input-offset input-length) (< 0 room))
    (mv :act 3 input-offset (min quantum (min room (- input-length input-offset)))))
((and (< fed copied) (< 0 room))
    (mv :act 2 fed (min quantum (min room (- copied fed)))))
((or (not (equal ssl 1)) (< fed copied) (< input-offset input-length) (zp room))
    (mv :act 7 0 0))
(t (mv :act 6 0 (min quantum room)))))))

(defthm fn2-tls-transport-plan-quantum
 (implies (equal (mv-nth 0 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) :act)
  (and (natp (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))
       (<= (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) quantum))))

(defthm fn2-tls-transport-plan-copy-bound
 (implies (and (equal (mv-nth 0 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) :act)
               (equal (mv-nth 1 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)) 1))
  (<= (+ (mv-nth 2 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))
         (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum))) total)))

(defthm fn2-tls-transport-plan-widths
 (and (unsigned-byte-p 8 (mv-nth 1 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))
      (unsigned-byte-p 32 (mv-nth 2 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))
      (unsigned-byte-p 32 (mv-nth 3 (fn2-tls-transport-plan total copied fed il io ol oo ssl room pending quantum)))))
(defcodec-transport-upgrade fn2-tls-transport fn2-tls-transport-plan :status-field ssl-status)

(defun fn2-tls-transport-observe (cap nonce slot generation serial code count errno fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil
  :guard (and (fn2-tls-transport-wfp fn2-tls-transport) (= (fn2-tls-transport-rows fn2-tls-transport) 1))))
 ;; Malformed/stale returns change neither the pending action nor its ledger.
 (if (member-equal (fn2-tls-transport-pending 0 fn2-tls-transport) '(1 8 9))
     (fn2-tls-transport-observe-lifecycle cap nonce slot generation serial code count errno fn2-tls-transport)
 (if (not (and (fn2-tls-transport-match-p cap nonce slot generation serial fn2-tls-transport)
               (integerp code) (unsigned-byte-p 64 (abs code))
               (unsigned-byte-p 32 count) (unsigned-byte-p 32 errno)))
     (mv :stale nil fn2-tls-transport)
  (let* ((action (fn2-tls-transport-pending 0 fn2-tls-transport))
         (offset (fn2-tls-transport-offset 0 fn2-tls-transport))
         (requested (fn2-tls-transport-requested 0 fn2-tls-transport))
         (copied (fn2-tls-transport-copied 0 fn2-tls-transport))
         (il (fn2-tls-transport-input-length 0 fn2-tls-transport))
         (ol (fn2-tls-transport-output-length 0 fn2-tls-transport))
         (fn2-tls-transport (fn2-tls-transport-put 0
           (raw-negative (if (< code 0) 1 0)) (raw-code (abs code))
           (raw-count count) (raw-errno errno) (pending 0))))
   (cond


    ((equal action 7)
     (if (and (member-equal code '(0 1 2)) (= count 0))
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (ssl-status code))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((and (member-equal action '(5 6)) (< code 0) (member-equal errno '(4 11 35)))
     (mv :blocked nil fn2-tls-transport))
    ((not (and (fn2-codec-transfer-counts-p code 0 requested 0) (= count 0)
               (unsigned-byte-p 32 (+ offset code))
               (or (not (member-equal action '(5 6))) (< 0 code))))
     (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport)))

    ((equal action 2)
     (if (<= (+ offset code) copied)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (fed (+ offset code)) (ssl-status 5))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((equal action 3)
     (if (<= (+ offset code) il)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (input-offset (+ offset code)) (ssl-status 5))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((equal action 4) (let ((fn2-tls-transport (fn2-tls-transport-put 0 (output-length code) (output-offset 0))))
 (mv :ok t fn2-tls-transport)))
    ((equal action 5)
     (if (<= (+ offset code) ol)
         (let ((fn2-tls-transport (fn2-tls-transport-put 0 (output-offset (+ offset code)))))
 (mv :ok t fn2-tls-transport))
       (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))
    ((equal action 6) (let ((fn2-tls-transport (fn2-tls-transport-put 0 (input-length code) (input-offset 0))))
 (mv :ok t fn2-tls-transport)))
    (t (let ((fn2-tls-transport (fn2-tls-transport-put 0 (terminal 2))))
 (mv :closing t fn2-tls-transport))))))))







(defun fn2-tls-transport-status-kick (status)
 (declare (xargs :guard t))
 (eq status :closing))

(defun fn2-tls-transport-action-interest (action)
 (declare (xargs :guard t))
 (if (equal action 5) 4 1))



(verify-guards fn2-tls-transport-start)



(verify-guards fn2-tls-transport-observe
 :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (theory 'fn2-tls-transport-readers)))))

(verify-guards fn2-tls-transport-retire
 :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (theory 'fn2-tls-transport-readers)))))

(verify-guards fn2-tls-transport-handle
 :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (theory 'fn2-tls-transport-readers)))))

(verify-guards fn2-tls-transport-selected-p
 :hints (("Goal" :in-theory (set-difference-theories (current-theory :here) (theory 'fn2-tls-transport-readers)))))

(deftheory fn2-tls-transport-abstraction
 (union-theories '(fn2-tls-transport-plan) (theory 'fn2-tls-transport-readers)))

(local (in-theory
 (set-difference-theories (current-theory :here) (theory 'fn2-tls-transport-abstraction))))



(defthm fn2-tls-transport-observe-wfp
 (implies (and (fn2-tls-transportp fn2-tls-transport)
               (= (fn2-tls-transport-rows fn2-tls-transport) 1)
               (fn2-tls-transport-wfp fn2-tls-transport))
  (fn2-tls-transport-wfp
   (mv-nth 2 (fn2-tls-transport-observe cap nonce slot generation serial code count errno fn2-tls-transport))))
 :hints (("Goal" :in-theory (disable fn2-tls-transport-rows))))



(assert-event
 (fn2-assert-compliant-p
  '(fn2-tls-transport-start fn2-tls-transport-next fn2-tls-transport-observe
    fn2-tls-transport-handoff fn2-tls-transport-retire fn2-tls-transport-handle fn2-tls-transport-selected-p fn2-tls-transport-status-kick fn2-tls-transport-action-interest) (w state)))
