; Buffered-word dimensions, independent of word values and digest typing.
(in-package "ACL2")
(include-book "blake3-row-frames")
(include-book "columns-observation-frames")
(fn2-book-layer :b)
(local (include-book "arithmetic-3/floor-mod/floor-mod" :dir :system))

; Public observation rules reuse each actual setter's unconditional NTH
; interface, so bounded writers can keep WORDS-LENGTH opaque.
(defcolumns-array-length-frames fn2-b3 fn2-b3-words)

; Only STORE writes this array. Its physical stripe bound is deliberately
; weaker than READY or a stobj recognizer, and is preserved by scalar writes.
(defun fn2-b3-word-stripep (row fn2-b3)
 (declare (xargs :stobjs fn2-b3 :guard t))
 (and (natp row) (<= (* 16 (+ 1 row)) (fn2-b3-words-length fn2-b3))))

(defun fn2-b3-word-frame-event (name domain world)
 (declare (xargs :verify-guards nil))
 (let* ((args (getpropc name 'formals nil world))
        (outputs (getpropc name 'stobjs-out nil world))
        (position (position-eq 'fn2-b3 outputs))
        (call (cons name args))
        (result (if (equal (len outputs) 1) call `(mv-nth ,position ,call)))
        (claim `(equal (fn2-b3-words-length ,result)
                       (fn2-b3-words-length fn2-b3)))
        (observation (getpropc 'fn2-b3-words-length 'unnormalized-body nil world))
        ; SUBLIS-VAR accepts translated terms, unlike the public event syntax.
        (raw-result (if (equal (len outputs) 1) call `(mv-nth ',position ,call)))
        (raw-claim (and (pseudo-termp observation) (pseudo-termp raw-result)
                        `(equal ,(sublis-var (list (cons 'fn2-b3 raw-result)) observation)
                                ,observation)))
        (hyps (append (and domain '((fn2-b3-word-stripep row fn2-b3)))
                      (and (eq domain :index) '((natp i) (<= i 16)))))
        (recursive (getpropc name 'recursivep nil world)))
  (if (or (not observation) (not raw-claim)
          (not (equal (getpropc 'fn2-b3-words-length 'formals nil world) '(fn2-b3)))
          (not (equal (getpropc 'fn2-b3-words-length 'stobjs-in nil world) '(fn2-b3)))
          (not (equal (getpropc 'fn2-b3-words-length 'stobjs-out :missing world) '(nil)))
          (eq (getpropc 'fn2-b3-words-length 'symbol-class nil world) :program)
          (not (member-eq 'fn2-b3 args)) (not position)
          (not (member-eq domain '(nil :stripe :index)))
          (and domain (not (member-eq 'row args)))
          (and (eq domain :index) (not (member-eq 'i args))))
      (er hard 'fn2-b3-word-frame-event "Invalid actual B3 frame ABI/domain: ~x0 ~x1." name domain)
   `(progn
     (defthm ,(fn2-columns-sym name "-WORD-FRAME")
      ,(if hyps `(implies (and ,@hyps) ,claim) claim)
      :hints (("Goal" ,@(and recursive `(:induct ,call))
               :in-theory (e/d (,name fn2-b3-word-stripep
                                ,@(and (not domain) '(fn2-b3-words-length)))
                               (fn2-b3-rows
                                ,@(and domain '(fn2-b3-words-length)))))))
     ; Setter-NTH laws normalize the observation before a callee frame can
     ; match. Publish that exact projection as a consequence of the public
     ; interface, with identical hypotheses and the callee body still closed.
     (defthm ,(fn2-columns-sym name "-WORD-FRAME-RAW-BY-DEFINITION")
      ,(if hyps `(implies (and ,@hyps) ,raw-claim) raw-claim)
      :hints (("Goal" :use ,(fn2-columns-sym name "-WORD-FRAME")
               :in-theory (e/d (fn2-b3-words-length)
                               (,name fn2-b3-word-stripep
                                ,(fn2-columns-sym name "-WORD-FRAME"))))))))))
(defmacro fn2-b3-word-frame (name &optional domain)
 `(make-event (value (fn2-b3-word-frame-event ',name ',domain (w state)))))

(defthm fn2-b3-store-word-frame
 (implies (and (fn2-b3-word-stripep row fn2-b3) (natp i) (< i 16))
  (equal (fn2-b3-words-length (fn2-b3-store row i v fn2-b3))
         (fn2-b3-words-length fn2-b3)))
 :hints (("Goal" :in-theory (enable fn2-b3-store fn2-b3-word-stripep fn2-b3-words-length))))

; Scalar-only paths need no typing or stripe hypothesis at all. The producer
; exposes WORDS-LENGTH there so existing public SET-*-NTH rules apply; no
; duplicated setter matrix or scalar implementation unfolding is needed.
(fn2-b3-word-frame fn2-b3-init)
(fn2-b3-word-frame fn2-b3-push)
(fn2-b3-word-frame fn2-b3-flush)
; BYTE normalizes POS modulo 64; POOL-MESSAGE traverses indices [i,16).
; Their callers retain the physical stripe after each returned update.
(fn2-b3-word-frame fn2-b3-byte :stripe)
(fn2-b3-word-frame fn2-b3-pool-message :index)
(fn2-b3-word-frame fn2-b3-chunk-output-into :stripe)
(fn2-b3-word-frame fn2-b3-bulk :stripe)
(fn2-b3-word-frame fn2-b3-span :stripe)
(fn2-b3-word-frame fn2-b3-fragment-into :stripe)
(fn2-b3-word-frame fn2-b3-feed :stripe)
(fn2-b3-word-frame fn2-b3-update :stripe)

(defthm fn2-b3-ready-word-stripe
 (implies (fn2-b3-ready row fn2-b3 fn2-digests)
          (fn2-b3-word-stripep row fn2-b3))
 :hints (("Goal" :in-theory (enable fn2-b3-ready fn2-b3-word-stripep))))
(in-theory (disable fn2-b3-word-stripep))
