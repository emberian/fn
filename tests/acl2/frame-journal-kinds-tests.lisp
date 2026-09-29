; Row K3: a new journal kind is one table row and adds no guard proof.
;
; The FNWF table grows here by thirteen hypothetical kinds (24 in all, the
; real eleven first), and the protected-prefix function, its record
; recognizer and that recognizer's field lemma are restated over the grown
; table with exactly the hints books/frame-journal and books/frame use.  Each
; is admitted under a step limit near what the eleven-kind proof costs
; (8,625 steps for `fn-frame-workflow-protected''s guard), so the cost does
; not grow with the kinds: the generic table facts
; (`fn-frame-spec-for-is-spec-list', `fn-frame-spec-for-has-code',
; `fn-frame-enum-index-is-octet') decide a constant table by evaluation.
; The tooth: the same guard with the recognizer and the code lookup open --
; the proof before K3, which split on every kind (475,868 steps at eleven)
; -- does not prove within 300,000 steps.

(in-package "ACL2")
(include-book "../../books/frame")
(include-book "must-fail-checked")

; The theory books/frame proves its entry points' guards in.
(local (in-theory (enable fn-cbor-invariants-vocabulary
                          fn-frame-octet-vocabulary
                          fn-frame-fields-vocabulary
                          fn-frame-journal-vocabulary)))

(defconst *fn-frame-k3-kinds*
  (append *fn-frame-workflow-kinds*
          '(:k3-a :k3-b :k3-c :k3-d :k3-e :k3-f :k3-g :k3-h :k3-i :k3-j
            :k3-k :k3-l :k3-m)))

(defconst *fn-frame-k3-specs*
  (append *fn-frame-workflow-specs*
          (list (cons :k3-a '(:text :nat)) (cons :k3-b '(:nat))
                (cons :k3-c '(:text :text)) (cons :k3-d '(:nat :nat :text))
                (cons :k3-e '(:text :text :text)) (cons :k3-f '(:text :nat :nat))
                (cons :k3-g '(:text)) (cons :k3-h '(:nat :text))
                (cons :k3-i '(:text :text :nat))
                (cons :k3-j (list :text (cons :enum *fn-frame-phases*)))
                (cons :k3-k '(:nat :nat)) (cons :k3-l '(:text :nat))
                (cons :k3-m '(:nat :text :text)))))

(assert-event (and (equal (len *fn-frame-k3-kinds*) 24)
                   (fn-frame-spec-tablep *fn-frame-k3-specs*)
                   (fn-frame-table-kinds-in *fn-frame-k3-specs*
                                            *fn-frame-k3-kinds*)
                   (<= (fn-frame-table-width *fn-frame-k3-specs*)
                       *fn-frame-max-workflow-payload*))
              :msg "K3: the grown table is well formed")

(defun fn-frame-k3-record-okp (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (let ((spec (fn-frame-spec-for kind *fn-frame-k3-specs*)))
    (and (not (equal spec :none))
         (fn-frame-values-okp spec values)
         (or (not (equal kind :outcome))
             (fn-frame-outcome-pairp (fn-frame-item 2 values)
                                     (fn-frame-item 3 values))))))

(with-prover-step-limit 20000 (verify-guards fn-frame-k3-record-okp))

(with-prover-step-limit 20000
  (defthm fn-frame-k3-record-okp-fields
    (implies (fn-frame-k3-record-okp kind values)
             (and (fn-frame-spec-listp
                   (fn-frame-spec-for kind *fn-frame-k3-specs*))
                  (fn-frame-values-okp
                   (fn-frame-spec-for kind *fn-frame-k3-specs*) values)))
    :rule-classes :forward-chaining
    :hints (("Goal" :in-theory (e/d (fn-frame-k3-record-okp
                                     fn-frame-spec-for-is-spec-list)
                                    (fn-frame-spec-for fn-frame-values-okp
                                     fn-frame-spec-listp))))))

(defun fn-frame-k3-protected (kind values)
  (declare (xargs :guard t :verify-guards nil))
  (if (not (fn-frame-k3-record-okp kind values))
      :bad
    (let ((code (fn-frame-enum-index kind *fn-frame-k3-kinds*))
          (payload (fn-frame-fields-octets
                    (fn-frame-spec-for kind *fn-frame-k3-specs*) values)))
      (if (or (equal code 0)
              (not (fn-cbor-at-mostp payload *fn-frame-max-workflow-payload*)))
          :bad
        (fn-frame-protected *fn-frame-magic-workflow* *fn-frame-version* code
                            payload)))))

; The tooth first (the definition is still unverified): opened, the proof
; splits on every kind.
(must-fail-checked
 (verify-guards fn-frame-k3-protected
   :hints (("Goal" :in-theory (e/d (fn-frame-k3-record-okp fn-frame-enum-index)
                                   (fn-frame-spec-for fn-frame-values-okp
                                    fn-frame-fields-octets
                                    fn-frame-spec-for-is-spec-list
                                    fn-frame-spec-for-has-code
                                    fn-frame-enum-index-is-octet))))))

; The positive witness: the real hint, 24 kinds, the eleven-kind budget.
(with-prover-step-limit 20000
  (verify-guards fn-frame-k3-protected
    :hints (("Goal" :in-theory (e/d (fn-frame-k3-record-okp-fields
                                     fn-frame-spec-for-is-spec-list
                                     fn-frame-spec-for-has-code
                                     fn-frame-enum-index-is-octet)
                                    (fn-frame-k3-record-okp
                                     fn-frame-spec-for fn-frame-values-okp
                                     fn-frame-fields-octets
                                     fn-frame-enum-index))))))

; A new kind encodes, with the code its row's position gives it.
(assert-event
 (let ((p (fn-frame-k3-protected :k3-m (list 7 (list 65) (list 66 67)))))
   (and (consp p)
        (equal (nth 5 p) 24)))
 :msg "K3: witness, the twenty-fourth kind encodes with code 24")

; Hypotheses of the generic facts, affirmatively: a table row whose
; specification is not a spec list, and a row whose kind has no code.
(assert-event
 (let ((bad (list (cons :x '(:no-such-field)))))
   (and (not (fn-frame-spec-tablep bad))
        (not (equal (fn-frame-spec-for :x bad) :none))
        (not (fn-frame-spec-listp (fn-frame-spec-for :x bad)))))
 :msg "fn-frame-spec-for-is-spec-list: without fn-frame-spec-tablep")
(assert-event
 (let ((table (list (cons :x '(:nat)))))
   (and (not (fn-frame-table-kinds-in table '(:y)))
        (not (equal (fn-frame-spec-for :x table) :none))
        (equal (fn-frame-enum-index :x '(:y)) 0)))
 :msg "fn-frame-spec-for-has-code: without fn-frame-table-kinds-in")
(assert-event
 (let ((keys (make-list 256 :initial-element :z)))
   (and (not (<= (len keys) 255))
        (not (fn-cbor-octetp (fn-frame-enum-index :w (append keys '(:w)))))))
 :msg "fn-frame-enum-index-is-octet: without the 255-kind bound")
