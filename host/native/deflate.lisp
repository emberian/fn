;;; fn native host: the NNTP COMPRESS DEFLATE layer's two halves (lane
;;; compress; RFC 8054).  Loaded after io.lisp and lz4.lisp by
;;; host/native/build.lisp.
;;;
;;; INBOUND: the client's raw DEFLATE stream is decoded by ACL2
;;; (books/deflate-inflate.lisp fn-zin-feed, PRF-909/910).  This file holds a
;;; connection's private buffers for it (the state stobj, the 32 KiB window,
;;; the table, the output and the input) and calls the entry; every octet the
;;; served step sees is one ACL2 produced, within the per-call bound LIM and
;;; the stream's ratio bound, and a refused stream is named by ACL2's line.
;;;
;;; OUTBOUND: lib/libfn-deflate beside the image's core (tools/build_deflate.sh
;;; over the vendored zlib 1.3.2, third_party/zlib/UPSTREAM.txt), or the file
;;; FN_DEFLATE_LIBRARY names; host/native/fn-deflate.c is its one entry.  It
;;; compresses the reply windows ACL2 rendered, with a sync flush after each.
;;; A fault there garbles only what the server sends.  The parameters are
;;; ACL2's (books/nntp-compress.lisp fn-zc-deflate-params).

(in-package "ACL2")

(define-condition fnn-deflate-unsupported (error)
  ((detail :initarg :detail :reader fnn-deflate-detail))
  (:report (lambda (c s) (format s "DEFLATE compressor unavailable: ~a" (fnn-deflate-detail c)))))

;; The pinned vendored version (third_party/zlib/UPSTREAM.txt): 1.3.2.
(defconstant +fnn-deflate-version+ #x1320)

(defvar *fnn-deflate-state* :uninitialized)
(defvar *fnn-deflate-library* nil)
(defvar *fnn-deflate-lock* (sb-thread:make-mutex :name "fn DEFLATE initialization"))

(defun fnn-deflate-library-name ()
  (if (member :darwin *features*) "libfn-deflate.dylib" "libfn-deflate.so"))

(defun fnn-deflate-library-candidates ()
  "FN_DEFLATE_LIBRARY when the operator names one, else lib/ beside the core."
  (let ((named (sb-ext:posix-getenv "FN_DEFLATE_LIBRARY"))
        (core sb-ext:*core-pathname*))
    (cond ((and named (plusp (length named)))
           (if (find (code-char 0) named)
               (error 'fnn-deflate-unsupported :detail "invalid FN_DEFLATE_LIBRARY")
             (list named)))
          (core
           (list (namestring
                  (merge-pathnames (concatenate 'string "lib/" (fnn-deflate-library-name))
                                   (make-pathname :name nil :type nil :version nil
                                                  :defaults core)))))
          (t nil))))

(sb-alien:define-alien-routine ("fn_deflate_new" fnn-%deflate-new) sb-sys:system-area-pointer
  (level sb-alien:int) (window-bits sb-alien:int) (mem-level sb-alien:int))
(sb-alien:define-alien-routine ("fn_deflate_bound" fnn-%deflate-bound) sb-alien:long
  (h sb-sys:system-area-pointer) (src-len sb-alien:long))
(sb-alien:define-alien-routine ("fn_deflate_sync" fnn-%deflate-sync) sb-alien:long
  (h sb-sys:system-area-pointer)
  (src (* sb-alien:unsigned-char)) (src-len sb-alien:long)
  (dst (* sb-alien:unsigned-char)) (dst-cap sb-alien:long))
(sb-alien:define-alien-routine ("fn_deflate_free" fnn-%deflate-free) sb-alien:void
  (h sb-sys:system-area-pointer))
(sb-alien:define-alien-routine ("fn_deflate_version" fnn-%deflate-version) sb-alien:int)

(defun fnn-deflate-initialize ()
  "Load lib/libfn-deflate once and check its version is the pinned one."
  (sb-thread:with-mutex (*fnn-deflate-lock*)
    (case *fnn-deflate-state*
      (:ready t)
      (:unsupported (error 'fnn-deflate-unsupported :detail "the library did not load"))
      (t
       (let ((last-error nil) (loaded nil))
         (dolist (candidate (fnn-deflate-library-candidates))
           (unless loaded
             (handler-case
                 (progn (sb-alien:load-shared-object candidate :dont-save t)
                        (setq loaded candidate))
               (error (condition) (setq last-error condition)))))
         (unless loaded
           (setq *fnn-deflate-state* :unsupported)
           (error 'fnn-deflate-unsupported
                  :detail (if last-error (format nil "~a" last-error)
                            "no lib/libfn-deflate beside the core")))
         (let ((version (fnn-%deflate-version)))
           (unless (eql version +fnn-deflate-version+)
             (setq *fnn-deflate-state* :unsupported)
             (error 'fnn-deflate-unsupported
                    :detail (format nil "~a is version ~x, not the pinned ~x"
                                    loaded version +fnn-deflate-version+))))
         (setq *fnn-deflate-library* loaded
               *fnn-deflate-state* :ready)
         t)))))

(defun fnn-deflate-reset ()
  "A restarted image re-loads the library from its own lib/ (:dont-save)."
  (sb-thread:with-mutex (*fnn-deflate-lock*)
    (setq *fnn-deflate-state* :uninitialized *fnn-deflate-library* nil))
  t)

;;; ---------------------------------------------------------------------------
;;; The outbound stream of one connection.

(defstruct (fnn-zout (:constructor %make-fnn-zout)) handle)

(defun fnn-zout-new ()
  "A raw-DEFLATE stream with ACL2's parameters (level window-bits
mem-level), or a store fault when zlib refuses them or memory runs out."
  (fnn-deflate-initialize)
  (destructuring-bind (level window-bits mem-level) (fnn-core 'fn-zc-deflate-params)
    (let ((h (fnn-%deflate-new level window-bits mem-level)))
      (when (zerop (sb-sys:sap-int h))
        (error 'fnn-owner-connection-fault :operation :compress
               :cause (format nil "zlib refused the stream (~a ~a ~a)" level window-bits mem-level)))
      (%make-fnn-zout :handle h))))

(defun fnn-zout-free (zout)
  (when (and zout (fnn-zout-handle zout))
    (fnn-%deflate-free (fnn-zout-handle zout))
    (setf (fnn-zout-handle zout) nil))
  nil)

(defun fnn-zout-sync (zout octets)
  "OCTETS (a byte vector ACL2 rendered) compressed and sync-flushed: the
octets to send.  A failure is a fault on this connection (the stream is
unusable after it)."
  (let* ((h (or (fnn-zout-handle zout)
                (error 'fnn-owner-connection-fault :operation :compress
                       :cause "the stream is closed")))
         (src (coerce octets '(simple-array (unsigned-byte 8) (*))))
         ;; ACL2's room for one sync-flushed window (books/nntp-compress.lisp
         ;; fn-zc-sync-output-octets): output that does not fit is
         ;; fn_deflate_sync's -2, a fault on this connection, never a cut.
         (cap (fnn-core 'fn-zc-sync-output-octets (length src))))
    (unless (and (integerp cap) (plusp cap))
      (error 'fnn-owner-connection-fault :operation :compress
             :cause (format nil "no bound for ~a octets" (length src))))
    (let* ((dst (make-array cap :element-type '(unsigned-byte 8)))
           (got (sb-sys:with-pinned-objects (src dst)
                  (fnn-%deflate-sync
                   h
                   (sb-alien:sap-alien (sb-sys:vector-sap src) (* sb-alien:unsigned-char))
                   (length src)
                   (sb-alien:sap-alien (sb-sys:vector-sap dst) (* sb-alien:unsigned-char))
                   cap))))
      (if (>= got 0)
          (subseq dst 0 got)
        (error 'fnn-owner-connection-fault :operation :compress
               :cause (format nil "zlib failed (code ~a)" got))))))

;;; ---------------------------------------------------------------------------
;;; A stored payload's candidate (books/payload-deflate.lisp; the append,
;;; host/native/io.lisp fnn-log-compress).  UNTRUSTED: ACL2's decision
;;; (fn-lzr-append-decide) runs the proved decoder over it before anything
;;; is taken.
;;;
;;; The encoder is this image's own SBCL deflater (fnn-ldf-, lane compress-7;
;;; ember's gate, planning/review-2026-09-29-gpt6-decisions.md section 6,
;;; measured in planning/evidence/deflater-gate-2026-09-29/result.md: on the
;;; 9,733 held-out 20news articles, baseline 1, one finished stream each, its
;;; CPU cost is 1.84 x zlib 9's at a ratio of 2.1437 against 2.1432, every
;;; stream inflating exactly).  RFC 1951 raw DEFLATE: LZ77 over hash chains
;;; with zlib's lazy evaluation and level-9 search limits, then per block the
;;; cheapest of dynamic Huffman, fixed Huffman and stored.  Bounds, by
;;; construction: two 32 Ki-entry chain tables and a 16 Ki-symbol block
;;; buffer per call, with the dictionary and the span copied once; at most
;;; MAX-CHAIN candidates per position (a quarter once a GOOD-LENGTH match is
;;; in hand), each compared over at most 258 octets.  It shares no state
;;; across calls: the dictionary is the caller's, per call.  The wire's
;;; COMPRESS stream stays zlib's (above).


(deftype fnn-ldf-octets () '(simple-array (unsigned-byte 8) (*)))
(deftype fnn-ldf-u16v () '(simple-array (unsigned-byte 16) (*)))
(deftype fnn-ldf-fixv () '(simple-array fixnum (*)))
(deftype fnn-ldf-idx () '(mod 1152921504606846976))

(defconstant +fnn-ldf-wsize+ 32768)
(defconstant +fnn-ldf-wmask+ 32767)
(defconstant +fnn-ldf-hmask+ 32767)
(defconstant +fnn-ldf-block-symbols+ 16384)

;; (GOOD-LENGTH MAX-LAZY NICE-LENGTH MAX-CHAIN): zlib's configuration_table.
(defparameter *fnn-ldf-levels*
  #((4 4 8 4) (4 5 16 8) (4 6 32 32) (4 4 16 16) (8 16 32 32)
    (8 16 128 128) (8 32 128 256) (32 128 258 1024) (32 258 258 4096)))
(defvar *fnn-ldf-level* 9)

;;; ---------------------------------------------------------------------------
;;; Tables (RFC 1951 3.2.5)

(defun fnn-ldf-make-u16 (n) (make-array n :element-type '(unsigned-byte 16) :initial-element 0))
(defun fnn-ldf-make-fix (n) (make-array n :element-type 'fixnum :initial-element 0))

(defparameter *fnn-ldf-len-base* (fnn-ldf-make-u16 29))
(defparameter *fnn-ldf-len-extra* (fnn-ldf-make-u16 29))
(defparameter *fnn-ldf-dist-base* (fnn-ldf-make-u16 30))
(defparameter *fnn-ldf-dist-extra* (fnn-ldf-make-u16 30))
(defparameter *fnn-ldf-len-code* (fnn-ldf-make-u16 256))     ; length-3 -> 0..28
(defparameter *fnn-ldf-dist-small* (fnn-ldf-make-u16 256))   ; dist-1 < 256 -> code
(defparameter *fnn-ldf-dist-large* (fnn-ldf-make-u16 256))   ; (dist-1)>>7 -> code

(let ((base 3))
  (dotimes (i 28)
    (let ((e (if (< i 8) 0 (floor (- i 4) 4))))
      (setf (aref *fnn-ldf-len-base* i) base (aref *fnn-ldf-len-extra* i) e)
      (dotimes (k (ash 1 e)) (when (< (+ base k -3) 256) (setf (aref *fnn-ldf-len-code* (+ base k -3)) i)))
      (incf base (ash 1 e))))
  (setf (aref *fnn-ldf-len-base* 28) 258 (aref *fnn-ldf-len-extra* 28) 0 (aref *fnn-ldf-len-code* 255) 28))
(let ((base 1))
  (dotimes (i 30)
    (let ((e (if (< i 4) 0 (floor (- i 2) 2))))
      (setf (aref *fnn-ldf-dist-base* i) base (aref *fnn-ldf-dist-extra* i) e)
      (dotimes (k (ash 1 e))
        (let ((d1 (+ base k -1)))
          (if (< d1 256)
              (setf (aref *fnn-ldf-dist-small* d1) i)
              (setf (aref *fnn-ldf-dist-large* (ash d1 -7)) i))))
      (incf base (ash 1 e)))))

(declaim (inline fnn-ldf-dist-code))
(defun fnn-ldf-dist-code (d)
  (declare (type (integer 1 32768) d))
  (let ((d1 (1- d)))
    (if (< d1 256) (aref (the fnn-ldf-u16v *fnn-ldf-dist-small*) d1) (aref (the fnn-ldf-u16v *fnn-ldf-dist-large*) (ash d1 -7)))))

;;; ---------------------------------------------------------------------------
;;; Bit output (LSB first)

(defstruct (fnn-ldf-bw (:constructor fnn-ldf-make-bw (out)))
  (out (make-array 0 :element-type '(unsigned-byte 8)) :type fnn-ldf-octets)
  (pos 0 :type fnn-ldf-idx)
  (buf 0 :type (unsigned-byte 62))
  (cnt 0 :type (integer 0 62)))

(declaim (inline fnn-ldf-put-bits))
(defun fnn-ldf-put-bits (fnn-ldf-bw v n)
  (declare (optimize (speed 3) (safety 1) (debug 0)))
  (declare (type fnn-ldf-bw fnn-ldf-bw) (type (unsigned-byte 24) v) (type (integer 0 24) n))
  (let ((buf (logior (fnn-ldf-bw-buf fnn-ldf-bw) (ash v (fnn-ldf-bw-cnt fnn-ldf-bw)))) (cnt (+ (fnn-ldf-bw-cnt fnn-ldf-bw) n)))
    (declare (type (unsigned-byte 62) buf) (type (integer 0 62) cnt))
    (loop while (>= cnt 8)
          do (let ((out (fnn-ldf-bw-out fnn-ldf-bw)) (pos (fnn-ldf-bw-pos fnn-ldf-bw)))
               (when (>= pos (length out))
                 (let ((new (make-array (* 2 (max 64 (length out))) :element-type '(unsigned-byte 8))))
                   (replace new out) (setf (fnn-ldf-bw-out fnn-ldf-bw) new out new)))
               (setf (aref out pos) (logand buf 255) (fnn-ldf-bw-pos fnn-ldf-bw) (1+ pos))
               (setf buf (ash buf -8) cnt (- cnt 8))))
    (setf (fnn-ldf-bw-buf fnn-ldf-bw) buf (fnn-ldf-bw-cnt fnn-ldf-bw) cnt)))

(defun fnn-ldf-align-byte (fnn-ldf-bw)
  (when (plusp (fnn-ldf-bw-cnt fnn-ldf-bw)) (fnn-ldf-put-bits fnn-ldf-bw 0 (- 8 (fnn-ldf-bw-cnt fnn-ldf-bw)))))

;;; ---------------------------------------------------------------------------
;;; Huffman code lengths, limited to LIMIT bits

(defun fnn-ldf-huffman-lengths (freq limit)
  (declare (optimize (speed 3) (safety 1) (debug 0)))
  "Code lengths for the symbols FREQ counts, none over LIMIT, at least two
symbols coded (zlib's rule: a decoder may refuse a one-code tree)."
  (declare (type fnn-ldf-fixv freq) (type (integer 1 15) limit))
  (let* ((n (length freq))
         (lens (make-array n :element-type '(unsigned-byte 8) :initial-element 0))
         (syms (loop for s below n when (plusp (aref freq s)) collect s)))
    (when (< (length syms) 2)
      (setf syms (sort (remove-duplicates (append syms (list 0 1))) #'<))
      (dolist (s syms) (setf (aref lens s) 1))
      (return-from fnn-ldf-huffman-lengths lens))
    (setf syms (sort syms (lambda (a b) (let ((fa (aref freq a)) (fb (aref freq b)))
                                          (or (< fa fb) (and (= fa fb) (< a b)))))))
    (let* ((m (length syms))
           (weight (fnn-ldf-make-fix (* 2 m)))
           (parent (fnn-ldf-make-fix (* 2 m)))
           (depth (fnn-ldf-make-fix (* 2 m)))
           (leaf 0) (inner m) (next m))
      (declare (type fixnum m leaf inner next))
      (loop for s in syms for i fixnum from 0 do (setf (aref weight i) (aref freq s)))
      (flet ((fnn-ldf-take ()
               (if (and (< leaf m) (or (>= inner next) (<= (aref weight leaf) (aref weight inner))))
                   (prog1 leaf (incf leaf))
                   (prog1 inner (incf inner)))))
        (loop while (< next (1- (* 2 m)))
              do (let ((a (fnn-ldf-take)) (b (fnn-ldf-take)))
                   (setf (aref weight next) (+ (aref weight a) (aref weight b))
                         (aref parent a) next (aref parent b) next)
                   (incf next))))
      (let ((root (- (* 2 m) 2)))
        (setf (aref depth root) 0)
        (loop for i from (1- root) downto 0
              do (setf (aref depth i) (1+ (aref depth (aref parent i))))))
      (loop for s in syms for i from 0 do (setf (aref lens s) (min limit (aref depth i))))
      ;; Kraft repair: lengthen the fnn-ldf-longest codes still under LIMIT.
      (let ((kraft (loop for s in syms sum (ash 1 (- limit (aref lens s))))))
        (loop while (> kraft (ash 1 limit))
              do (let ((best nil))
                   (dolist (s syms)
                     (when (and (< (aref lens s) limit)
                                (or (null best) (> (aref lens s) (aref lens best))
                                    (and (= (aref lens s) (aref lens best))
                                         (< (aref freq s) (aref freq best)))))
                       (setf best s)))
                   (decf kraft (ash 1 (- limit (aref lens best) 1)))
                   (incf (aref lens best)))))
      lens)))

(defun fnn-ldf-canonical-codes (lens)
  "The bit-reversed canonical codes of LENS (RFC 1951 3.2.2), ready to emit LSB first."
  (let* ((n (length lens)) (codes (fnn-ldf-make-u16 n)) (count (fnn-ldf-make-fix 16)) (next (fnn-ldf-make-fix 16)))
    (loop for l across lens when (plusp l) do (incf (aref count l)))
    (let ((code 0))
      (loop for bits from 1 to 15
            do (setf code (ash (+ code (aref count (1- bits))) 1)
                     (aref next bits) code)))
    (dotimes (s n)
      (let ((l (aref lens s)))
        (when (plusp l)
          (let ((c (aref next l)) (r 0))
            (incf (aref next l))
            (dotimes (k l) (setf r (logior (ash r 1) (logand (ash c (- k)) 1))))
            (setf (aref codes s) r)))))
    codes))

;;; ---------------------------------------------------------------------------
;;; Blocks

(defparameter *fnn-ldf-fixed-lit-lens*
  (let ((l (make-array 288 :element-type '(unsigned-byte 8))))
    (dotimes (i 288) (setf (aref l i) (cond ((< i 144) 8) ((< i 256) 9) ((< i 280) 7) (t 8))))
    l))
(defparameter *fnn-ldf-fixed-dist-lens* (make-array 30 :element-type '(unsigned-byte 8) :initial-element 5))
(defparameter *fnn-ldf-fixed-lit-codes* (fnn-ldf-canonical-codes *fnn-ldf-fixed-lit-lens*))
(defparameter *fnn-ldf-fixed-dist-codes* (fnn-ldf-canonical-codes *fnn-ldf-fixed-dist-lens*))
(defparameter *fnn-ldf-clen-order* #(16 17 18 0 8 7 9 6 10 5 11 4 12 3 13 2 14 1 15))

(defun fnn-ldf-rle-lengths (lens)
  "The code-length alphabet's symbols for LENS: a list of (SYMBOL EXTRA-VALUE)."
  (let ((out '()) (n (length lens)) (i 0))
    (loop while (< i n)
          do (let* ((l (aref lens i))
                    (run (loop for j from i below n while (= (aref lens j) l) count t)))
               (incf i run)
               (if (zerop l)
                   (progn
                     (loop while (>= run 11) do (let ((k (min run 138))) (push (list 18 (- k 11)) out) (decf run k)))
                     (when (>= run 3) (push (list 17 (- run 3)) out) (setf run 0))
                     (loop repeat run do (push (list 0 0) out)))
                   (progn
                     (push (list l 0) out) (decf run)
                     (loop while (>= run 3) do (let ((k (min run 6))) (push (list 16 (- k 3)) out) (decf run k)))
                     (loop repeat run do (push (list l 0) out))))))
    (nreverse out)))

(defun fnn-ldf-clen-extra-bits (sym) (case sym (16 2) (17 3) (18 7) (t 0)))

(defun fnn-ldf-emit-block (fnn-ldf-bw w start end lit dist nsym final)
  (declare (optimize (speed 3) (safety 1) (debug 0)))
  "Emit the NSYM symbols (LIT: literal/length-3+256 flag in DIST) covering
W[START, END) as the cheapest of dynamic, fixed and stored."
  (declare (type fnn-ldf-bw fnn-ldf-bw) (type fnn-ldf-octets w) (type fnn-ldf-idx start end nsym) (type fnn-ldf-u16v lit dist))
  (let ((lf (fnn-ldf-make-fix 286)) (df (fnn-ldf-make-fix 30)) (extra 0))
    (declare (type fixnum extra))
    (dotimes (i nsym)
      (let ((d (aref dist i)))
        (if (zerop d)
            (incf (aref lf (aref lit i)))
            (let ((lc (aref (the fnn-ldf-u16v *fnn-ldf-len-code*) (aref lit i))) (dc (fnn-ldf-dist-code d)))
              (incf (aref lf (+ 257 lc))) (incf (aref df dc))
              (incf extra (+ (aref (the fnn-ldf-u16v *fnn-ldf-len-extra*) lc) (aref (the fnn-ldf-u16v *fnn-ldf-dist-extra*) dc)))))))
    (setf (aref lf 256) 1)
    (let* ((llens (fnn-ldf-huffman-lengths lf 15))
           (dlens (fnn-ldf-huffman-lengths df 15))
           (hlit (max 257 (1+ (or (position-if #'plusp llens :from-end t) 0))))
           (hdist (max 1 (1+ (or (position-if #'plusp dlens :from-end t) 0))))
           (all (concatenate '(simple-array (unsigned-byte 8) (*)) (subseq llens 0 hlit) (subseq dlens 0 hdist)))
           (rle (fnn-ldf-rle-lengths all))
           (cf (fnn-ldf-make-fix 19)))
      (dolist (r rle) (incf (aref cf (first r))))
      (let* ((clens (fnn-ldf-huffman-lengths cf 7))
             (hclen (max 4 (1+ (or (position-if (lambda (s) (plusp (aref clens s))) *fnn-ldf-clen-order* :from-end t) 0))))
             (dyn (+ 3 14 (* 3 hclen)
                     (loop for r in rle sum (+ (aref clens (first r)) (fnn-ldf-clen-extra-bits (first r))))
                     (loop for s below 286 sum (* (aref lf s) (aref llens s)))
                     (loop for s below 30 sum (* (aref df s) (aref dlens s)))
                     extra))
             (fix (+ 3 (loop for s below 286 sum (* (aref lf s) (aref *fnn-ldf-fixed-lit-lens* s)))
                     (* 5 (loop for s below 30 sum (aref df s))) extra))
             (raw (- end start))
             (sto (if (<= raw 65535) (+ (* 8 (ceiling (+ (fnn-ldf-bw-cnt fnn-ldf-bw) 3) 8)) 32 (* 8 raw) (- (fnn-ldf-bw-cnt fnn-ldf-bw))) nil)))
        (cond
          ((and sto (<= sto dyn) (<= sto fix))
           (fnn-ldf-put-bits fnn-ldf-bw (if final 1 0) 3) (fnn-ldf-align-byte fnn-ldf-bw)
           (fnn-ldf-put-bits fnn-ldf-bw (logand raw 65535) 16) (fnn-ldf-put-bits fnn-ldf-bw (logxor raw 65535) 16)
           (loop for p from start below end do (fnn-ldf-put-bits fnn-ldf-bw (aref w p) 8)))
          (t
           (let (lcodes dcodes llen dlen)
             (if (< dyn fix)
                 (let ((ccodes (fnn-ldf-canonical-codes clens)))
                   (fnn-ldf-put-bits fnn-ldf-bw (if final 5 4) 3)
                   (fnn-ldf-put-bits fnn-ldf-bw (- hlit 257) 5) (fnn-ldf-put-bits fnn-ldf-bw (- hdist 1) 5) (fnn-ldf-put-bits fnn-ldf-bw (- hclen 4) 4)
                   (dotimes (k hclen) (fnn-ldf-put-bits fnn-ldf-bw (aref clens (aref *fnn-ldf-clen-order* k)) 3))
                   (dolist (r rle)
                     (fnn-ldf-put-bits fnn-ldf-bw (aref ccodes (first r)) (aref clens (first r)))
                     (let ((e (fnn-ldf-clen-extra-bits (first r)))) (when (plusp e) (fnn-ldf-put-bits fnn-ldf-bw (second r) e))))
                   (setf lcodes (fnn-ldf-canonical-codes llens) dcodes (fnn-ldf-canonical-codes dlens) llen llens dlen dlens))
                 (progn
                   (fnn-ldf-put-bits fnn-ldf-bw (if final 3 2) 3)
                   (setf lcodes *fnn-ldf-fixed-lit-codes* dcodes *fnn-ldf-fixed-dist-codes*
                         llen *fnn-ldf-fixed-lit-lens* dlen *fnn-ldf-fixed-dist-lens*)))
             (let ((lcodes lcodes) (dcodes dcodes) (llen llen) (dlen dlen))
               (declare (type fnn-ldf-u16v lcodes dcodes) (type fnn-ldf-octets llen dlen))
               (dotimes (i nsym)
                 (let ((d (aref dist i)) (v (aref lit i)))
                   (if (zerop d)
                       (fnn-ldf-put-bits fnn-ldf-bw (aref lcodes v) (aref llen v))
                       (let* ((lc (aref (the fnn-ldf-u16v *fnn-ldf-len-code*) v)) (dc (fnn-ldf-dist-code d))
                              (le (aref (the fnn-ldf-u16v *fnn-ldf-len-extra*) lc)) (de (aref (the fnn-ldf-u16v *fnn-ldf-dist-extra*) dc)))
                         (fnn-ldf-put-bits fnn-ldf-bw (aref lcodes (+ 257 lc)) (aref llen (+ 257 lc)))
                         (when (plusp le) (fnn-ldf-put-bits fnn-ldf-bw (- (+ v 3) (aref (the fnn-ldf-u16v *fnn-ldf-len-base*) lc)) le))
                         (fnn-ldf-put-bits fnn-ldf-bw (aref dcodes dc) (aref dlen dc))
                         (when (plusp de) (fnn-ldf-put-bits fnn-ldf-bw (- d (aref (the fnn-ldf-u16v *fnn-ldf-dist-base*) dc)) de))))))
               (fnn-ldf-put-bits fnn-ldf-bw (aref lcodes 256) (aref llen 256))))))))))

;;; ---------------------------------------------------------------------------
;;; LZ77 with lazy evaluation (zlib's deflate_slow)

(defun fnn-ldf-deflate-payload (dict src &key (level *fnn-ldf-level*))
  (declare (optimize (speed 3) (safety 1) (debug 0)))
  "Raw DEFLATE of SRC (fnn-ldf-octets) over the preset DICT (fnn-ldf-octets, at most 32 KiB
used), finished (BFINAL on the last block): an octet vector."
  (declare (type fnn-ldf-octets dict src))
  (destructuring-bind (good-length max-lazy nice-length max-chain) (coerce (aref *fnn-ldf-levels* (1- level)) 'list)
    (declare (type fixnum good-length max-lazy nice-length max-chain))
    (let* ((dl (min (length dict) +fnn-ldf-wsize+))
           (w (let ((v (make-array (+ dl (length src)) :element-type '(unsigned-byte 8))))
                (replace v dict :start2 (- (length dict) dl)) (replace v src :start1 dl) v))
           (n (length w))
           (head (make-array (1+ +fnn-ldf-hmask+) :element-type 'fixnum :initial-element 0))
           (prev (make-array +fnn-ldf-wsize+ :element-type 'fixnum :initial-element 0))
           (lit (fnn-ldf-make-u16 +fnn-ldf-block-symbols+))
           (dist (fnn-ldf-make-u16 +fnn-ldf-block-symbols+))
           (nsym 0) (block-start dl)
           (fnn-ldf-bw (fnn-ldf-make-bw (make-array (+ 64 (length src) (ash (length src) -3)) :element-type '(unsigned-byte 8)))))
      (declare (type fnn-ldf-octets w) (type fnn-ldf-fixv head prev) (type fnn-ldf-u16v lit dist) (type fnn-ldf-idx n nsym block-start))
      (labels ((fnn-ldf-hash (p) (declare (type fnn-ldf-idx p))
                 (logand (logxor (ash (aref w p) 10) (ash (aref w (+ p 1)) 5) (aref w (+ p 2))) +fnn-ldf-hmask+))
               (fnn-ldf-insert (p) (declare (type fnn-ldf-idx p))
                 ;; the previous head for P's fnn-ldf-hash (P+1 stored; 0 = none), and P becomes the head
                 (let* ((h (fnn-ldf-hash p)) (old (aref head h)))
                   (setf (aref prev (logand p +fnn-ldf-wmask+)) old (aref head h) (1+ p))
                   old))
               (fnn-ldf-longest (p cand best)
                 (declare (type fnn-ldf-idx p) (type fixnum cand best))
                 (let* ((maxlen (min 258 (- n p)))
                        (limit (- p +fnn-ldf-wsize+))
                        (chain (if (>= best good-length) (ash max-chain -2) max-chain))
                        (best-dist 0))
                   (declare (type fixnum maxlen limit chain best-dist))
                   (loop while (and (>= cand 0) (> cand limit) (plusp chain))
                         do (when (and (< best maxlen)
                                       (= (aref w (+ cand best)) (aref w (+ p best)))
                                       (= (aref w cand) (aref w p)))
                              (let ((len (loop for k fixnum from 0 below maxlen
                                               while (= (aref w (+ cand k)) (aref w (+ p k)))
                                               finally (return k))))
                                (declare (type fixnum len))
                                (when (> len best)
                                  (setf best len best-dist (- p cand))
                                  (when (>= len nice-length) (return)))))
                            (decf chain)
                            (let ((next (1- (aref prev (logand cand +fnn-ldf-wmask+)))))
                              (declare (type fixnum next))
                              (if (< next cand) (setf cand next) (return))))
                   (values best best-dist)))
               (fnn-ldf-flush (end final)
                 (fnn-ldf-emit-block fnn-ldf-bw w block-start end lit dist nsym final)
                 (setf nsym 0 block-start end))
               (fnn-ldf-emit-lit (p) (declare (type fnn-ldf-idx p))
                 (setf (aref lit nsym) (aref w p) (aref dist nsym) 0) (incf nsym)
                 (when (= nsym +fnn-ldf-block-symbols+) (fnn-ldf-flush (1+ p) nil)))
               (fnn-ldf-emit-match (p len d) (declare (type fnn-ldf-idx p len d))
                 (setf (aref lit nsym) (- len 3) (aref dist nsym) d) (incf nsym)
                 (when (= nsym +fnn-ldf-block-symbols+) (fnn-ldf-flush (+ p len) nil))))
        (loop for p from (max 0 (- dl +fnn-ldf-wsize+)) below (- dl 2) do (fnn-ldf-insert p))
        (let ((p dl) (prev-len 2) (prev-dist 0) (available nil))
          (declare (type fixnum p prev-len prev-dist))
          (loop while (< p n)
                do (let ((cur-len 2) (cur-dist 0))
                     (declare (type fixnum cur-len cur-dist))
                     (when (< (+ p 2) n)
                       (let ((cand (1- (fnn-ldf-insert p))))
                         (when (and (>= cand 0) (< prev-len max-lazy) (<= (- p cand) +fnn-ldf-wsize+))
                           (multiple-value-setq (cur-len cur-dist) (fnn-ldf-longest p cand 2))
                           (when (and (= cur-len 3) (> cur-dist 4096)) (setf cur-len 2)))))
                     (cond
                       ((and (>= prev-len 3) (<= cur-len prev-len))
                        (let ((mstart (1- p)))
                          (fnn-ldf-emit-match mstart prev-len prev-dist)
                          (loop for q from (1+ p) below (+ mstart prev-len)
                                when (< (+ q 2) n) do (fnn-ldf-insert q))
                          (setf p (+ mstart prev-len) available nil prev-len 2)))
                       (available
                        (fnn-ldf-emit-lit (1- p))
                        (setf prev-len cur-len prev-dist cur-dist) (incf p))
                       (t (setf available t prev-len cur-len prev-dist cur-dist) (incf p)))))
          (when available (fnn-ldf-emit-lit (1- p)))
          (fnn-ldf-flush n t)
          (fnn-ldf-align-byte fnn-ldf-bw)
          (subseq (fnn-ldf-bw-out fnn-ldf-bw) 0 (fnn-ldf-bw-pos fnn-ldf-bw)))))))

;; `fnn-deflate-candidate' keeps its contract: SRC's octets [START,
;; START+N) over the preset DICT, in at most CAP octets, else :NONE.
(defun fnn-deflate-candidate (dict src start n cap)
  "The stream for SRC's octets [START, START+N) over the preset DICT (an
octet vector), in at most CAP octets: an octet vector, or :NONE when no
stream fits CAP (ACL2's policy reads it as no gain)."
  (unless (and (integerp start) (integerp n) (<= 0 start) (<= 0 n) (<= (+ start n) (length src)))
    (fnn-fault "deflate-encoder: the span is not inside the record"))
  (when (<= cap 0) (return-from fnn-deflate-candidate :none))
  (let ((z (fnn-ldf-deflate-payload
            (coerce dict '(simple-array (unsigned-byte 8) (*)))
            (coerce (subseq src start (+ start n)) '(simple-array (unsigned-byte 8) (*))))))
    (if (<= (length z) cap) z :none)))

;;; The served read of a stored payload (host/native/extent.lisp
;;; fn-durable-realize-lz): ACL2's payload decoder over buffers the host
;;; keeps in a pool (fn-zpl-decode-bufs, books/deflate-pool.lisp; KEYSTONES
;;; fn-zpl-decode-bufs-is-decode and fn-zpl-decode-bufs-is-the-lz-value: an
;;; :ok answer is the value A-DURABLE-LZ names).  Each buffer set carries
;;; ACL2's POOL value, NIL when the set is made and afterwards only what the
;;; entry returned (the invariant fn-zpl-pool-okp holds of NIL and the
;;; entry re-establishes it): the window keeps its dictionary, and a payload
;;; over the same dictionary re-zeroes only the ring cells the last one
;;; wrote.

(defvar *fnn-pzd-pool* nil)
(defvar *fnn-pzd-lock* (sb-thread:make-mutex :name "fn payload decoder buffers"))

(defun fnn-pzd-buffers ()
  "A buffer set (IN WIN TAB OUT POOL): one from the pool, else a new one
whose POOL is NIL."
  (or (sb-thread:with-mutex (*fnn-pzd-lock*) (pop *fnn-pzd-pool*))
      (let ((sizes (fnn-core 'fn-zin-buffer-sizes)))
        (list (fnn-zin-private-octets 4096)
              (fnn-zin-private-octets (getf sizes :window))
              (fnn-zin-private-octets (getf sizes :table))
              (fnn-zin-private-octets 4096)
              nil))))

(defun fnn-pzd-decode (dict c n)
  "ACL2's decode of the stored stream C (octets, a list) over the dictionary
DICT (a list) to N octets: (:ok . OCTET-LIST) or ACL2's (:error WHY)."
  (let* ((bufs (fnn-pzd-buffers))
         (in (first bufs))
         (m (length c)))
    (fn-octets$c-reserve m in)
    (replace (the fnn-octets (svref in 0)) c)
    (setf (svref in 1) m)
    (destructuring-bind (answer pool win tab out)
        (fnn-call 'fn-zpl-decode-bufs (fifth bufs) dict m n in (second bufs) (third bufs)
                  (fourth bufs))
      (prog1 (if (and (consp answer) (eq (first answer) :ok))
                 (cons :ok (coerce (subseq (svref out 0) 0 (svref out 1)) 'list))
               answer)
        (sb-thread:with-mutex (*fnn-pzd-lock*)
          (push (list in win tab out pool) *fnn-pzd-pool*))))))

;;; ---------------------------------------------------------------------------
;;; The inbound stream of one connection: ACL2's inflater over private
;;; buffers.

(defstruct (fnn-zin (:constructor %make-fnn-zin))
  st win tab out in
  ;; compressed octets received and not yet consumed (after a :full stop)
  (pending nil))

(defun fnn-zin-private-octets (n)
  (fn-octets$c-reserve n (create-fn-octets$c)))

(defun fnn-zin-new ()
  "A connection's inflater, reset, its window and table at their fixed
lengths (ACL2's fn-zin-reset and fn-zin-buffers-ready)."
  (let* ((sizes (fnn-core 'fn-zin-buffer-sizes))
         (zin (%make-fnn-zin :st (create-fn-zin-st)
                             :win (fnn-zin-private-octets (getf sizes :window))
                             :tab (fnn-zin-private-octets (getf sizes :table))
                             :out (fnn-zin-private-octets 4096)
                             :in (fnn-zin-private-octets 4096))))
    (setf (fnn-zin-st zin) (first (fnn-call 'fn-zin-reset (fnn-zin-st zin))))
    (destructuring-bind (win tab) (fnn-call 'fn-zin-buffers-ready (fnn-zin-win zin) (fnn-zin-tab zin))
      (setf (fnn-zin-win zin) win (fnn-zin-tab zin) tab))
    zin))

(defun fnn-zin-fill-input (zin octets)
  (let* ((buf (fnn-zin-in zin)) (n (length octets)))
    (fn-octets$c-reserve n buf)
    (replace (the fnn-octets (svref buf 0)) octets)
    (setf (svref buf 1) n)
    buf))

(defun fnn-zin-inflate (zin octets lim)
  "Feed the compressed OCTETS (appended to what an earlier call left) to
ACL2's inflater with output bound LIM: (values PLAINTEXT STATUS), PLAINTEXT
a byte vector of at most LIM octets, STATUS :more (every octet taken; read
more), :full (LIM reached; octets remain pending for the next call) or the
refusal's line (a string: the connection closes).  The budget covers the
whole call (at most one action per input bit and per output octet, plus the
table builds), so :yield only loops."
  (let* ((input (if (fnn-zin-pending zin)
                    (concatenate '(simple-array (unsigned-byte 8) (*)) (fnn-zin-pending zin) octets)
                  octets))
         (n (length input))
         (buf (fnn-zin-fill-input zin input))
         (out (fnn-zin-out zin))
         (ip 0))
    (setf (svref out 1) 0)
    (loop
      (destructuring-bind (status b2 ip2 st win tab out2)
          (fnn-call 'fn-zin-feed (+ 1024 (* 16 (- n ip)) (* 2 lim)) (fnn-zin-st zin) ip n lim
                    buf (fnn-zin-win zin) (fnn-zin-tab zin) out)
        (declare (ignore b2))
        (setf (fnn-zin-st zin) st (fnn-zin-win zin) win (fnn-zin-tab zin) tab
              (fnn-zin-out zin) out2 out out2)
        (unless (and (integerp ip2) (<= ip ip2 n))
          (fnn-fault "compress: ACL2 returned a malformed input position"))
        (setq ip ip2)
        (case status
          (:yield nil)
          ((:more :full)
           (setf (fnn-zin-pending zin) (if (< ip n) (subseq input ip) nil))
           (return (values (subseq (svref out2 0) 0 (svref out2 1)) status)))
          (t
           (setf (fnn-zin-pending zin) nil)
           (return (values (subseq (svref out2 0) 0 (svref out2 1))
                           (if (and (consp status) (eq (first status) :refused))
                               (fnn-core 'fn-zin-refusal-text (second status))
                             "compress-fault: the inflater answered no status")))))))))
