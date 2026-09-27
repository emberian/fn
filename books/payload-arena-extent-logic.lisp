; fn: the payload arena's EXTENT seal, its logical side (lane
; arena-offheap-2, 2026-09-27; PRF-281; the design is
; planning/evidence/arena-offheap-2026-09-27.md section 3).
;
; Stage 2 of arena-offheap moves payloads off the heap: a handle may denote
; an EXTENT of a durable file (a log segment the host holds open) instead of
; octets the process holds.  The arena's logical value does not change: it
; is the list of sealed payloads, and an extent handle's payload is
; `fn-durable-octets' of its extent (books/assumptions.lisp, A-DURABLE-EXTENT).
;
; This book is the logical side the generic (books/payload-arena.lisp) and
; the extent implementation (books/payload-arena-extent.lisp) share:
;   fn-arn-extentp E              E = (FILE EOFF ELEN POFF PLEN TRAILER), six
;                                 naturals, the payload [POFF, POFF+PLEN)
;                                 inside the entry's protected prefix
;                                 [EOFF, EOFF+ELEN);
;   fn-arena$a-seal-extent ...    (append a (list (fn-durable-octets FILE POFF PLEN)));
;   fn-arx-realize-down           the payload built octet by octet through the
;                                 host's realizer, proved equal to
;                                 fn-durable-octets (fn-arx-realize-is-durable).

(in-package "ACL2")
(include-book "payload-arena-bytes")
(include-book "assumptions")

(defun fn-arn-extentp (e)
  (declare (xargs :guard t))
  (and (true-listp e)
       (equal (len e) 6)
       (natp (nth 0 e)) (natp (nth 1 e)) (natp (nth 2 e))
       (natp (nth 3 e)) (natp (nth 4 e)) (natp (nth 5 e))
       (<= (nth 1 e) (nth 3 e))
       (<= (+ (nth 3 e) (nth 4 e)) (+ (nth 1 e) (nth 2 e)))))

(defun fn-arn-extent-guardp (file eoff elen poff plen trailer)
  (declare (xargs :guard t))
  (and (natp file) (natp eoff) (natp elen) (natp poff) (natp plen) (natp trailer)
       (<= eoff poff) (<= (+ poff plen) (+ eoff elen))))

(defthm fn-arn-extentp-of-list
  (equal (fn-arn-extentp (list file eoff elen poff plen trailer))
         (fn-arn-extent-guardp file eoff elen poff plen trailer)))

(defun fn-arena$a-seal-extent (file eoff elen poff plen trailer fn-arena$a)
  (declare (xargs :guard (fn-arn-extent-guardp file eoff elen poff plen trailer))
           (ignore eoff elen trailer))
  (fn-oct-snoc fn-arena$a (fn-durable-octets file poff plen)))

; The payload through the realizer: octets [0, I) consed onto ACC, from the
; top down (one realizer call per octet; the host's realizer answers from its
; cache of the entry).
(defun fn-arx-realize-down (i file eoff elen poff plen trailer acc)
  (declare (xargs :guard (and (natp i) (true-listp acc))))
  (if (zp i)
      acc
    (fn-arx-realize-down (1- i) file eoff elen poff plen trailer
                         (cons (fn-durable-realize-octet file eoff elen poff plen trailer (1- i))
                               acc))))

(local
 (defthm fn-arx-cons-nth-nthcdr
   (implies (and (posp i) (<= i (len l)))
            (equal (cons (nth (1- i) l) (nthcdr i l))
                   (nthcdr (1- i) l)))
   :hints (("Goal" :in-theory (enable nth nthcdr)))))

(local
 (defun fn-arx-dec-ind (i)
   (if (zp i) t (fn-arx-dec-ind (1- i)))))

(local
 (defthm fn-arx-realize-down-suffix
   (implies (and (natp i) (<= i (nfix plen)))
            (equal (fn-arx-realize-down i file eoff elen poff plen trailer
                                        (nthcdr i (fn-durable-octets file poff plen)))
                   (fn-durable-octets file poff plen)))
   :hints (("Goal" :induct (fn-arx-dec-ind i)))))

(local
 (defthm fn-arx-nthcdr-len
   (implies (and (true-listp l) (equal n (len l)))
            (equal (nthcdr n l) nil))))

(local
 (defthm fn-arx-octet-list-true-listp
   (implies (fn-cbor-octet-listp x) (true-listp x))))

(defthm fn-arx-realize-is-durable
  (implies (natp plen)
           (equal (fn-arx-realize-down plen file eoff elen poff plen trailer nil)
                  (fn-durable-octets file poff plen)))
  :hints (("Goal" :use ((:instance fn-arx-realize-down-suffix (i plen)))
           :in-theory (disable fn-arx-realize-down-suffix))))
