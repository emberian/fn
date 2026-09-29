; fn: the stored payload's codec, DEFLATE over a preset dictionary (lane
; compress, PRF-912, STO-037; the coordinator's Q15 decision of 2026-09-28:
; one DEFLATE inflater for the wire and the store).  Prefix `fn-pzd-'.
;
; A compressed payload is a raw DEFLATE stream (RFC 1951) made over one of
; the shipped preset dictionaries (books/payload-lz-dicts.lisp, by digest).
; `fn-pzd-decode dict c n' is what the frame books (books/payload-lz-record,
; -append, -replay, -value) take it to mean: (:ok OCTETS) when C decodes,
; over DICT, to exactly N octets and ends (its final block, or a sync flush
; at the end of its input), else
; (:error STATUS).  The decoder is the ACL2 inflater's payload decoder
; (books/deflate-inflate.lisp fn-zin-payload-with: bounded by a budget of
; actions, the bomb bound, and LIM = N + 1 octets of output); the encoder is
; zlib's (host/native/fn-deflate.c), untrusted: a seal keeps a candidate
; only when this decoder gives the payload's octets.
;
; The empty payload is the empty stream: (fn-pzd-decode dict nil 0) is
; (:ok nil) for every dictionary (`fn-pzd-decode-of-empty'), so a frame
; with an empty span needs no stream.
;
; THE HOST ENTRY.  `fn-pzd-decode-bufs' is the same decode over the host's
; buffers (the input in fn-octets, the thread's window, table and output):
; KEYSTONE `fn-pzd-decode-bufs-is-decode'.

(in-package "ACL2")
(include-book "deflate-inflate")

(defun fn-pzd-budget (clen n)
  ; Actions enough for any stream zlib writes: an action reads an input
  ; octet, emits an output octet, reads bits in hand, or builds a table.
  (declare (xargs :guard t))
  (+ 4096 (* 16 (nfix clen)) (* 2 (nfix n))))

; The stream's end: its final block ended (the inflater's mode 13, which
; the wire refuses by name, :stream-ended, and a payload ends with), or its
; input ran out after a sync flush (:more).
(defun fn-pzd-endedp (st)
  (declare (xargs :guard t))
  (or (eq st :more) (equal st '(:refused :stream-ended))))

(defun fn-pzd-answer (st out n)
  (declare (xargs :guard t))
  (if (and (fn-pzd-endedp st) (true-listp out) (equal (len out) (nfix n)))
      (list :ok out)
    (list :error (if (fn-pzd-endedp st) :length st))))

(defun fn-pzd-decode (dict c n)
  (declare (xargs :guard (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c) (natp n))))
  (if (and (zp n) (atom c))
      (list :ok nil)
    (let ((r (fn-zin-payload-with (fn-pzd-budget (len c) n) dict c (+ 1 (nfix n)))))
      (fn-pzd-answer (car r) (cadr r) n))))

(defthm fn-pzd-decode-shape
  (and (consp (fn-pzd-decode dict c n))
       (true-listp (fn-pzd-decode dict c n)))
  :rule-classes :type-prescription)

(defthm fn-pzd-decode-ok
  (implies (and (fn-cbor-octet-listp dict) (fn-cbor-octet-listp c)
                (equal (car (fn-pzd-decode dict c n)) :ok))
           (and (fn-cbor-octet-listp (cadr (fn-pzd-decode dict c n)))
                (true-listp (cadr (fn-pzd-decode dict c n)))
                (equal (len (cadr (fn-pzd-decode dict c n))) (nfix n))))
  :hints (("Goal" :in-theory (disable fn-zin-payload-with))))

(defthm fn-pzd-decode-of-empty
  (equal (fn-pzd-decode dict nil 0) (list :ok nil)))

(in-theory (disable fn-pzd-decode))

; -----------------------------------------------------------------------------
; The host entry: C in fn-octets cells [0, END); the answer, and the octets
; in fn-zin-out.  (mv ANSWER fn-zin-win fn-zin-tab fn-zin-out).

(defun fn-pzd-decode-bufs (dict end n fn-octets fn-zin-win fn-zin-tab fn-zin-out)
  (declare (xargs :stobjs (fn-octets fn-zin-win fn-zin-tab fn-zin-out)
                  :guard (and (fn-cbor-octet-listp dict) (natp end) (natp n)
                              (<= end (fn-octets-len fn-octets)))))
  (if (and (zp n) (zp end))
      (let ((fn-zin-out (fn-zin-out-clear fn-zin-out)))
        (mv (list :ok nil) fn-zin-win fn-zin-tab fn-zin-out))
    (mv-let (st fn-zin-win fn-zin-tab fn-zin-out)
      (fn-zin-payload-bufs (fn-pzd-budget end n) dict 0 end (+ 1 (nfix n)) fn-octets
                           fn-zin-win fn-zin-tab fn-zin-out)
      (let ((a (fn-pzd-answer st (fn-zin-out-list fn-zin-out) n)))
        (mv (if (eq (car a) :ok) (list :ok) a) fn-zin-win fn-zin-tab fn-zin-out)))))

(local
 (defthm fn-pzd-with-is-bufs
   (implies (fn-cbor-octet-listp c)
            (and (equal (car (fn-zin-payload-with b dict c lim))
                        (car (fn-zin-payload-bufs b dict 0 (len c) lim c nil nil nil)))
                 (equal (cadr (fn-zin-payload-with b dict c lim))
                        (mv-nth 3 (fn-zin-payload-bufs b dict 0 (len c) lim c nil nil nil)))))
   :hints (("Goal" :use ((:instance fn-zin-payload-bufs-is-payload-with
                                    (fn-zin-win nil) (fn-zin-tab nil) (fn-zin-out nil)))
            :in-theory (disable fn-zin-payload-bufs fn-zin-payload-with
                                fn-zin-payload-bufs-is-payload-with)))))

; KEYSTONE: the host entry answers the decoder's status, and on :ok its
; output buffer holds the decoder's octets.
(defthm fn-pzd-decode-bufs-is-decode
  (implies (and (fn-cbor-octet-listp c) (natp n))
           (let ((r (fn-pzd-decode-bufs dict (len c) n c fn-zin-win fn-zin-tab fn-zin-out))
                 (d (fn-pzd-decode dict c n)))
             (and (equal (car (car r)) (car d))
                  (implies (equal (car d) :ok)
                           (equal (mv-nth 3 r) (cadr d))))))
  :hints (("Goal" :in-theory (e/d (fn-pzd-decode) (fn-zin-payload-bufs fn-zin-payload-with))
           :expand ((len c)) :do-not-induct t)))

; -----------------------------------------------------------------------------
; A trivial encoder: X in stored blocks (RFC 1951 section 3.2.4), the last
; one final.  The witnesses use it as the candidate every payload has.

(defun fn-pzd-u16le (n)
  (declare (xargs :guard (natp n)))
  (list (mod (nfix n) 256) (mod (floor (nfix n) 256) 256)))

(local
 (defthm fn-pzd-len-nthcdr
   (implies (and (natp n) (<= n (len x)))
            (equal (len (nthcdr n x)) (- (len x) n)))
   :hints (("Goal" :in-theory (enable nthcdr len)))))

(defun fn-pzd-stored (x)
  (declare (xargs :guard (true-listp x) :measure (len x)))
  (if (<= (len x) 65535)
      (append (list 1) (fn-pzd-u16le (len x)) (fn-pzd-u16le (- 65535 (len x))) x)
    (append (list 0) (fn-pzd-u16le 65535) (fn-pzd-u16le 0) (take 65535 x)
            (fn-pzd-stored (nthcdr 65535 x)))))
