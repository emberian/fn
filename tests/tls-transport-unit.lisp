; The host-called next/observe pair, including short I/O and stale epochs.
(in-package "ACL2")
(include-book "../books/tls-transport")

(defun fn2-tls-transport-unit-run (steps fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil))
 (if (atom steps) (mv t fn2-tls-transport)
  (let* ((s (car steps)) (room (nth 0 s)) (pending (nth 1 s)))
   (mv-let (status action offset count serial fn2-tls-transport)
    (fn2-tls-transport-next room pending fn2-tls-transport)
    (let ((selected (equal (list status action offset count) (cons :act (take 3 (nthcdr 2 s))))))
     (mv-let (observed kick fn2-tls-transport)
      (fn2-tls-transport-observe 17 3 9 serial (nth 5 s) 0 (nth 6 s) fn2-tls-transport)
      (declare (ignore kick))
      (let ((valid (and selected (equal observed (nth 7 s))
                        (fn2-tls-transport-invariant fn2-tls-transport))))
       (mv-let (rest fn2-tls-transport) (fn2-tls-transport-unit-run (cdr steps) fn2-tls-transport)
        (mv (and valid rest) fn2-tls-transport)))))))))

(defun fn2-tls-transport-unit-retention (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil))
 (mv-let (start fn2-tls-transport) (fn2-tls-transport-start 17 3 9 8 8 4 20 fn2-tls-transport)
  (mv-let (ok fn2-tls-transport)
   (fn2-tls-transport-unit-run
    '((3 0 1 0 4 4 0 :ok) ; copy both chunks before any SSL call
      (3 0 1 4 4 4 0 :ok)
      (3 0 2 0 3 2 0 :ok) ; partial BIO acceptance retains the suffix
      (0 5 4 0 4 4 0 :ok) ; drain at most one quantum
      (0 1 5 0 4 2 0 :ok) ; short send
      (0 1 5 2 2 -1 11 :blocked) ; no prefix loss on EAGAIN
      (0 1 5 2 2 2 0 :ok)
      (0 1 4 0 1 1 0 :ok)
      (0 0 5 0 1 1 0 :ok)
      (0 0 7 0 0 0 0 :ok)) ; library completion may leave staged seed
     fn2-tls-transport)
   (mv-let (done action offset count serial fn2-tls-transport)
    (fn2-tls-transport-next 0 0 fn2-tls-transport)
    (declare (ignore action offset count serial))
    (mv-let (handoff copied fed il io ol oo fn2-tls-transport)
     (fn2-tls-transport-handoff 17 3 9 fn2-tls-transport)
     (let ((first (and (eq start :ok) ok (eq done :done) (eq handoff :ok)
                      (= copied 8) (= fed 2) (= il io) (= ol oo))))
      (mv-let (duplicate c f a b d e fn2-tls-transport)
       (fn2-tls-transport-handoff 17 3 9 fn2-tls-transport)
       (declare (ignore c f a b d e))
       (mv (and first (eq duplicate :stale)) fn2-tls-transport))))))))
(assert-event
 (with-local-stobj fn2-tls-transport
  (mv-let (ok fn2-tls-transport) (fn2-tls-transport-unit-retention fn2-tls-transport) ok)))

(defun fn2-tls-transport-unit-stale (fn2-tls-transport)
 (declare (xargs :stobjs fn2-tls-transport :verify-guards nil))
 (mv-let (start fn2-tls-transport) (fn2-tls-transport-start 17 3 9 8 8 4 20 fn2-tls-transport)
  (mv-let (status action offset count serial fn2-tls-transport)
   (fn2-tls-transport-next 0 0 fn2-tls-transport)
   (declare (ignore action offset count))
   (mv-let (stale kick fn2-tls-transport)
    (fn2-tls-transport-observe 18 3 9 serial 4 0 0 fn2-tls-transport)
    (declare (ignore kick))
    (let ((unchanged (and (= (fn2-tls-transport-copied 0 fn2-tls-transport) 0)
                          (= (fn2-tls-transport-pending 0 fn2-tls-transport) 1))))
     (mv-let (valid kick fn2-tls-transport)
      (fn2-tls-transport-observe 17 3 9 serial 4 0 0 fn2-tls-transport)
      (declare (ignore kick))
      (mv-let (duplicate kick fn2-tls-transport)
       (fn2-tls-transport-observe 17 3 9 serial 4 0 0 fn2-tls-transport)
       (declare (ignore kick))
       (mv (and (eq start :ok) (eq status :act) (eq stale :stale) unchanged
                (eq valid :ok) (eq duplicate :stale)
                (= (fn2-tls-transport-copied 0 fn2-tls-transport) 4)) fn2-tls-transport))))))))
(assert-event
 (with-local-stobj fn2-tls-transport
  (mv-let (ok fn2-tls-transport) (fn2-tls-transport-unit-stale fn2-tls-transport) ok)))
