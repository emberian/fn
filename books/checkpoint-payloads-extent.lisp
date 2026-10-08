; fn: the payload file's read bridge to the extent realizer (lane s-cpl,
; 2026-10-07; CPL-OPEN-IS-EXTENT-REALIZE).
;
; The extent realizer (host/native/extent.lisp fnn-extent-entry) reads an
; entry's protected prefix [EOFF, EOFF+ELEN) into a buffer and the 32 octets
; after it, and decides fn-arx-entry-verdict-buffer (books/payload-extent-read.lisp):
; :ok exactly when the frame digest of the prefix is the trailer read and the
; trailer is the descriptor's commitment.  A payload frame
; (books/checkpoint-payloads.lisp) is that entry: the prefix is header ++
; payload (EOFF = ref offset - 37, ELEN = 37 + len, POFF = 37, PLEN = len),
; and its trailer is the frame digest of the prefix, because the frame's chain
; is empty.  The keystone: the realizer's verdict on a frame in the file, for
; the commitment of the trailer the append plan returns, is :ok.

(in-package "ACL2")
(include-book "checkpoint-payloads")
(include-book "payload-extent-read")

; KEYSTONE (CPL-OPEN-IS-EXTENT-REALIZE).  For a frame appended after PRE, the
; realizer's reads (the prefix at the ref's frame start, the 32 octets after
; it) pass the realizer's own verdict against the commitment of the trailer
; the plan returns: the verdict is :ok.
(defthm fn-cpl-ref-passes-the-extent-realizer
  (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p)
                (equal fn-octets (take (+ 37 (len p))
                                       (nthcdr (len pre) (append pre (fn-cpl-frame p) post)))))
           (equal (fn-arx-entry-verdict-buffer
                   (fn-arx-trailer-nat (fn-cpl-trailer p))
                   (take 32 (nthcdr (+ (len pre) 37 (len p))
                                    (append pre (fn-cpl-frame p) post)))
                   fn-octets)
                  :ok))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-arx-entry-verdict-buffer-ok-is-the-commitment
                            (expected (fn-arx-trailer-nat (fn-cpl-trailer p)))
                            (read (fn-cpl-trailer p)))
                 fn-cpl-trailer-shape fn-cpl-trailer-is-the-frame-digest fn-cpl-prefix-in-file
                 fn-cpl-trailer-in-file)
           :in-theory (disable fn-arx-entry-verdict-buffer-ok-is-the-commitment
                               fn-cpl-trailer-shape fn-cpl-trailer-is-the-frame-digest
                               fn-cpl-prefix-in-file fn-cpl-trailer-in-file
                               fn-arx-entry-verdict-buffer))))

; -----------------------------------------------------------------------------
; The descriptor the open seals for a ref, and that sealing it reads back the
; payload (books/payload-arena.lisp fn-arena-seal-extent; every offset is an
; ABSOLUTE offset into the file).
;
; For a ref (OFF LEN) and the frame's trailer octets TR:
;   FILE   the host's file number of checkpoint.payloads
;   EOFF   OFF - 37          the protected prefix (header ++ payload) starts
;   ELEN   37 + LEN          its length: the trailer is read AFTER it
;   POFF   OFF               the payload's first octet, absolute
;   PLEN   LEN
;   TRAILER (fn-arx-trailer-nat TR)  the commitment (fn-arx-trailer-nat packs
;                            the 32 trailer octets)
; (fn-cpl-extent file ref tr) is exactly that argument list.

(include-book "payload-arena")

(defun fn-cpl-extent (file ref tr)
  (declare (xargs :guard (and (true-listp ref) (true-listp tr))))
  (list file
        (- (fn-cpl-ref-offset ref) 37)
        (+ 37 (fn-cpl-ref-len ref))
        (fn-cpl-ref-offset ref)
        (fn-cpl-ref-len ref)
        (fn-arx-trailer-nat tr)))

; The durable file FILE holds the octet list F from offset 0 (A-DURABLE-EXTENT
; names the durable octets abstractly; this ties them to the model).
(defun fn-cpl-holdsp (file f i)
  (declare (xargs :guard (natp i)))
  (if (consp f)
      (and (equal (fn-durable-octet file i) (car f))
           (fn-cpl-holdsp file (cdr f) (+ 1 (nfix i))))
    t))

(local (defun cpl-ind-a (file f off len)
         (if (zp len) (list file f off) (cpl-ind-a file (cdr f) (+ 1 (nfix off)) (1- len)))))

(local
 (defthm cpl-holds-at
   (implies (and (fn-cpl-holdsp file f off) (natp off) (natp len) (<= len (len f)))
            (equal (fn-durable-octets file off len) (take len f)))
   :hints (("Goal" :induct (cpl-ind-a file f off len)
            :in-theory (enable fn-durable-octets-unfold)))))

(local (defun cpl-ind-s (f i k)
         (if (zp k) (list f i) (cpl-ind-s (cdr f) (+ 1 (nfix i)) (1- k)))))

(local
 (defthm cpl-holds-shift
   (implies (and (fn-cpl-holdsp file f i) (natp i) (natp k) (<= k (len f)))
            (fn-cpl-holdsp file (nthcdr k f) (+ i k)))
   :hints (("Goal" :induct (cpl-ind-s f i k)))))

(local (defthm cpl-e-len-nthcdr
         (implies (natp k) (equal (len (nthcdr k x)) (nfix (- (len x) k))))
         :hints (("Goal" :induct (nthcdr k x)))))

(local
 (defthm cpl-holds-gen
   (implies (and (fn-cpl-holdsp file f 0) (natp off) (natp len) (<= (+ off len) (len f)))
            (equal (fn-durable-octets file off len) (take len (nthcdr off f))))
   :hints (("Goal" :use ((:instance cpl-holds-shift (i 0) (k off))
                         (:instance cpl-holds-at (f (nthcdr off f)))
                         (:instance cpl-e-len-nthcdr (k off) (x f)))
            :in-theory (disable cpl-holds-shift cpl-holds-at cpl-e-len-nthcdr)))))

(local (defthm cpl-e-nthcdr-append (equal (nthcdr (len a) (append a b)) b)))
(local (defthm cpl-e-take-append
         (implies (and (true-listp a) (equal k (len a))) (equal (take k (append a b)) a))))
(local (defthm cpl-e-nthcdr-sum
         (implies (and (natp a) (natp b)) (equal (nthcdr (+ a b) x) (nthcdr b (nthcdr a x))))
         :hints (("Goal" :induct (nthcdr a x)))))

; The payload octets of a frame in a file, read at the ref's absolute offset.
(local
 (defthm cpl-payload-in-file
   (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p))
            (equal (take (len p) (nthcdr (+ 37 (len pre))
                                         (append pre (fn-cpl-frame p) post)))
                   p))
   :hints (("Goal" :do-not-induct t
            :use ((:instance fn-cpl-frame-layout)
                  (:instance cpl-e-nthcdr-sum (a (len pre)) (b 37)
                             (x (append pre (fn-cpl-frame p) post)))
                  (:instance cpl-e-nthcdr-append (a (fn-scc-header 0 1 (len p) 0))
                             (b (append p (fn-cpl-trailer p) post)))
                  (:instance cpl-e-take-append (a p) (k (len p))
                             (b (append (fn-cpl-trailer p) post)))
                  (:instance cpl-e-nthcdr-append (a pre) (b (append (fn-cpl-frame p) post))))
            :in-theory (disable cpl-e-nthcdr-sum cpl-e-nthcdr-append
                                cpl-e-take-append fn-cpl-frame fn-cpl-trailer fn-scc-header)))))

; KEYSTONE.  Sealing the descriptor of a ref into the payload arena denotes the
; payload: the new handle's payload is the octets the durable file holds at
; [OFF, OFF+LEN), which are the payload the plan appended (the file FILE holds
; the model file from offset 0: A-DURABLE-EXTENT's octets, named).
(defthm fn-cpl-seal-reads-back-the-payload
  (implies (and (true-listp pre) (true-listp post) (fn-cpl-payloadp p) (natp file)
                (fn-cpl-holdsp file (append pre (fn-cpl-frame p) post) 0))
           (let ((e (fn-cpl-extent file (list (+ 37 (len pre)) (len p))
                                   (fn-cpl-trailer p))))
             (and (fn-arn-extent-guardp (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e) (nth 4 e) (nth 5 e))
                  (equal (fn-arena-payload
                          (fn-arena-count fn-arena)
                          (fn-arena-seal-extent (nth 0 e) (nth 1 e) (nth 2 e) (nth 3 e)
                                                (nth 4 e) (nth 5 e) fn-arena))
                         p))))
  :hints (("Goal" :do-not-induct t
           :use ((:instance fn-arena-seal-extent-payload
                            (file file) (eoff (len pre)) (elen (+ 37 (len p)))
                            (poff (+ 37 (len pre))) (plen (len p))
                            (trailer (fn-arx-trailer-nat (fn-cpl-trailer p))))
                 (:instance cpl-holds-gen (f (append pre (fn-cpl-frame p) post))
                            (off (+ 37 (len pre))) (len (len p)))
                 cpl-payload-in-file fn-cpl-frame-len cpl-header-len)
           :in-theory (e/d (fn-cpl-extent fn-cpl-ref-offset fn-cpl-ref-len fn-arn-extent-guardp)
                           (fn-arena-seal-extent-payload cpl-holds-gen cpl-payload-in-file
                            fn-cpl-frame-len fn-cpl-frame fn-cpl-trailer)))))
