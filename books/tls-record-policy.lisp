; Bounded TLS record policy over shared capability staging and per-op progress.
(in-package "ACL2")
(include-book "codec-transport")
(fn2-book-layer :a)

; Status: 0 call SSL, 1 WANT_READ, 2 WANT_WRITE, 3 app prefix complete,
; 4 authenticated EOF, 5 failure. Progress epochs advance only on physical
; progress or SSL calls; a failed socket readiness attempt is not progress.
(defun fn2-tls-record-plan
 (writep extent source-progress sink-progress status seen progress
  copied fed il io ol oo room pending quantum)
 (declare (xargs :guard t))
 (if (not (and (booleanp writep) (unsigned-byte-p 32 extent)
               (natp source-progress) (<= source-progress extent)
               (natp sink-progress) (<= sink-progress extent)
               (member-equal status '(0 1 2 3 4 5))
               (unsigned-byte-p 60 seen) (unsigned-byte-p 60 progress)
               (unsigned-byte-p 32 copied) (natp fed) (<= fed copied)
               (unsigned-byte-p 32 il) (natp io) (<= io il)
               (unsigned-byte-p 32 ol) (natp oo) (<= oo ol)
               (unsigned-byte-p 32 room) (unsigned-byte-p 32 pending)
               (posp quantum) (unsigned-byte-p 32 quantum)))
     (mv :bounds 0 0 0)
  (let ((app-progress (if writep source-progress sink-progress)))
   (cond
    ((equal status 5) (mv :failed 0 0 app-progress))
    ((equal status 4) (mv :eof 0 0 app-progress))
    ((< oo ol) (mv :act 5 oo (min quantum (- ol oo))))
    ((< 0 pending) (mv :act 4 0 (min quantum pending)))
    ((or (equal status 3) (= app-progress extent)) (mv :done 0 0 app-progress))
    ((and (< fed copied) (< 0 room)) (mv :act 2 fed (min quantum (min room (- copied fed)))))
    ((and (< io il) (< 0 room)) (mv :act 3 io (min quantum (min room (- il io)))))
    ((and (= status 1) (= seen progress) (< 0 room))
     (mv :act 6 0 (min quantum room)))
    ; A WANT_WRITE with neither output nor intervening codec progress cannot
    ; be satisfied by this memory-BIO profile. Refuse instead of spinning.
    ((and (= status 2) (= seen progress)) (mv :failed 0 0 app-progress))
    (t (mv :act (if writep 13 12) app-progress (min quantum (- extent app-progress))))))))

; Preserve a valid reported byte prefix even when the SSL status violates its
; primitive contract. Such a result closes the operation; it never retries that
; prefix. The enclosing observer retains the exact raw packet separately.
(defun fn2-tls-record-result (writep raw count requested progress extent)
 (declare (xargs :guard t))
 (if (not (and (booleanp writep) (integerp raw)
               (unsigned-byte-p 32 extent) (natp progress) (<= progress extent)
               (natp requested) (<= requested (- extent progress))
               (natp count) (<= count requested)))
     (mv :bounds 5 0)
  (let ((next (+ progress count)))
   (cond
    ((and (= raw 0) (< 0 count))
     (mv :ok (if (and writep (< next extent)) 0 3) next))
    ((and (member-equal raw '(1 2)) (= count 0)) (mv :ok raw progress))
    ((and (= raw -1) (= count 0)) (mv :ok 5 progress))
    ((and (= raw 3) (= count 0)) (mv :ok (if writep 5 4) progress))
    (t (mv :contract 5 next))))))

(defthm fn2-tls-record-result-progress-bound
 (implies (not (equal (mv-nth 0 (fn2-tls-record-result writep raw count requested progress extent)) :bounds))
  (and (natp (mv-nth 2 (fn2-tls-record-result writep raw count requested progress extent)))
       (<= (mv-nth 2 (fn2-tls-record-result writep raw count requested progress extent)) extent))))
(defthm fn2-tls-record-plan-widths
 (and (unsigned-byte-p 8 (mv-nth 1 (fn2-tls-record-plan writep extent sp rp status seen progress copied fed il io ol oo room pending quantum)))
      (unsigned-byte-p 32 (mv-nth 2 (fn2-tls-record-plan writep extent sp rp status seen progress copied fed il io ol oo room pending quantum)))
      (unsigned-byte-p 32 (mv-nth 3 (fn2-tls-record-plan writep extent sp rp status seen progress copied fed il io ol oo room pending quantum)))))
