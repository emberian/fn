; fn: the served read's entry check over an octet buffer (lane
; arena-offheap-3, 2026-09-27; PRF-295, P3's first consumer).
;
; The realizer of an extent handle (host/native/extent.lisp) preads the log
; entry's protected prefix and its 32-octet trailer.  It used to hand ACL2
; the whole entry as an octet list (fn-arx-entry-ok, books/payload-extent.lisp:
; elen + 32 conses per read, SHA-256 by car/cdr); now it fills its own octet
; buffer `fn-octets-rd' with the prefix, in place, and ACL2 decides
; `fn-arx-entry-ok-buffer': the frame digest of the buffer
; (`fn-frame-digest-buffer', books/frame-digest-buffer.lisp, read by index)
; is the trailer.  KEYSTONE fn-arx-entry-ok-buffer-is-the-frame-check: that is
; the log's own frame check on the prefix's octets (the entry's trailer is
; fn-frame-digest of its protected prefix: books/store-log.lisp fn-lg-frame
; through fn-frame-seal), and fn-arx-entry-ok-buffer-of-durable: a faithful
; read of an intact entry passes.

(in-package "ACL2")
(include-book "frame-digest-buffer")
(include-book "payload-extent")

; The realizer's buffer: its own live object, congruent to fn-octets (the
; served attempt's buffer is never touched by a read of an extent handle).
(defabsstobj fn-octets-rd
  :foundation fn-octets$c
  :recognizer (fn-octets-rd-p :logic fn-octets$ap :exec fn-octets$cp)
  :creator (create-fn-octets-rd :logic create-fn-octets$a :exec create-fn-octets$c)
  :exports ((fn-octets-rd-len :logic fn-octets$a-len :exec fn-octets$c-len)
            (fn-octets-rd-get :logic fn-octets$a-get :exec fn-octets$c-get)
            (fn-octets-rd-put :logic fn-octets$a-put :exec fn-octets$c-put :protect t)
            (fn-octets-rd-append-octet :logic fn-octets$a-append-octet
                                       :exec fn-octets$c-append-octet :protect t)
            (fn-octets-rd-clear :logic fn-octets$a-clear :exec fn-octets$c-clear)
            (fn-octets-rd-reserve :logic fn-octets$a-reserve :exec fn-octets$c-reserve
                                  :protect t)
            (fn-octets-rd-list :logic fn-octets$a-list :exec fn-octets$c-list)
            (fn-octets-rd-from-list :logic fn-octets$a-from-list
                                    :exec fn-octets$c-from-list :protect t)
            (fn-octets-rd-append-list :logic fn-octets$a-append-list
                                      :exec fn-oct-write-list :protect t)
            (fn-octets-rd-append-back :logic fn-octets$a-append-back
                                      :exec fn-octets$c-append-back :protect t)
            (fn-octets-rd-get-word :logic fn-octets$a-get-word :exec fn-octets$c-get-word)
            (fn-octets-rd-append-word :logic fn-octets$a-append-word
                                      :exec fn-octets$c-append-word :protect t))
  :congruent-to fn-octets)

; The check the realizer asks: the buffer holds the entry's protected prefix,
; TRAILER the 32 octets read after it.
(defun fn-arx-entry-ok-buffer (trailer fn-octets)
  (declare (xargs :stobjs fn-octets :guard t))
  (equal (fn-frame-digest-buffer nil fn-octets) trailer))

; KEYSTONE (PRF-295).  The buffer check is the frame check on the prefix's
; octets: the host's check (host/native/extent.lisp fnn-extent-entry calls
; fn-arx-entry-ok-buffer over fn-octets-rd) decides what the list check on
; the same octets decides.
(defthm fn-arx-entry-ok-buffer-is-the-frame-check
  (equal (fn-arx-entry-ok-buffer trailer fn-octets)
         (equal (fn-frame-digest fn-octets) trailer)))

; A faithful read of an intact entry passes: the buffer holds the durable
; prefix, TRAILER the durable trailer, and the file's trailer is the frame
; digest of its prefix (what the log's append wrote, A-DURABLE-EXTENT).
(defthm fn-arx-entry-ok-buffer-of-durable
  (implies (equal (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)
                  (fn-frame-digest (fn-durable-octets file eoff elen)))
           (fn-arx-entry-ok-buffer (fn-durable-octets file (+ eoff elen) *fn-frame-trailer-octets*)
                                   (fn-durable-octets file eoff elen)))
  :hints (("Goal" :in-theory (disable fn-durable-octets-len))))
