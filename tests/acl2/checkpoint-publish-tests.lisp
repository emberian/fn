; Witnesses and teeth for books/checkpoint-publish.lisp.
;
; The witness drives the production transitions through a whole publication
; and selection of a first generation, then a second one, crashing at every
; phase with every choice, and recovers each image with the codec.  The
; digest is a host value (A-CRYPTO); the model only compares it.
(in-package "ACL2")
(include-book "../../books/checkpoint-publish")
(include-book "../../books/codec-attach")
(include-book "std/testing/must-fail" :dir :system)

(defconst *cpp-groups* '("fn.letters" "fn.test"))
(defconst *cpp-r0*
  (fn-record-make 0 0 0 "<cp0@example.invalid>" '(65 13 10)
                  '("fn.letters") "cp-pin-0" "cp-content-0" "cp-release-0" 2 841000000))
(defconst *cpp-r1*
  (fn-record-make 1 4 4 "<cp1@example.invalid>" '(66 13 10)
                  '("fn.test") "cp-pin-1" "cp-content-1" "cp-release-1" 3 841000000))
(defconst *cpp-digest* (make-list 32 :initial-element 0))
(defconst *cpp-prefix-0* (list *cpp-r0*))
(defconst *cpp-prefix-1* (list *cpp-r0* *cpp-r1*))
(defconst *cpp-cp-0*
  (fn-checkpoint-capture-value (fn-checkpoint-capture *cpp-groups* 10 *cpp-prefix-0* 3)))
(defconst *cpp-cp-1*
  (fn-checkpoint-capture-value (fn-checkpoint-capture *cpp-groups* 10 *cpp-prefix-1* 6)))

(assert-event (fn-cpp-capturablep *cpp-groups* 10 *cpp-prefix-0* 3 *cpp-digest*))
(assert-event (fn-cpp-capturablep *cpp-groups* 10 *cpp-prefix-1* 6 *cpp-digest*))

; -----------------------------------------------------------------------------
; A whole first publication and selection, named at every phase.

(defconst *cpp-s0* (fn-cpp-initial *cpp-groups* 10))
(defconst *cpp-s1* (fn-cpp-stage *cpp-s0* *cpp-prefix-0* 3 *cpp-digest*))
(defconst *cpp-s2* (fn-cpp-candidate-file-result *cpp-s1* :ok))
(defconst *cpp-s3* (fn-cpp-candidate-link-result *cpp-s2* :ok))
(defconst *cpp-s4* (fn-cpp-candidate-dir-result *cpp-s3* :ok))
(defconst *cpp-s5* (fn-cpp-select *cpp-s4*))
(defconst *cpp-s6* (fn-cpp-marker-file-result *cpp-s5* :ok))
(defconst *cpp-s7* (fn-cpp-marker-replace-result *cpp-s6* :ok))
(defconst *cpp-s8* (fn-cpp-marker-dir-result *cpp-s7* :ok))

(assert-event (equal (fn-cpp-phase *cpp-s1*) :candidate-staged))
(assert-event (equal (fn-cpp-phase *cpp-s2*) :candidate-data-durable))
(assert-event (equal (fn-cpp-phase *cpp-s3*) :candidate-attempted))
(assert-event (equal (fn-cpp-phase *cpp-s4*) :candidate-published))
(assert-event (equal (fn-cpp-phase *cpp-s5*) :marker-staged))
(assert-event (equal (fn-cpp-phase *cpp-s6*) :marker-data-durable))
(assert-event (equal (fn-cpp-phase *cpp-s7*) :marker-attempted))
(assert-event (equal (fn-cpp-phase *cpp-s8*) :idle))
(assert-event (and (fn-cpp-statep *cpp-s1*) (fn-cpp-statep *cpp-s2*)
                   (fn-cpp-statep *cpp-s3*) (fn-cpp-statep *cpp-s4*)
                   (fn-cpp-statep *cpp-s5*) (fn-cpp-statep *cpp-s6*)
                   (fn-cpp-statep *cpp-s7*) (fn-cpp-statep *cpp-s8*)))
; Authority is unchanged through every step but the last.
(assert-event (and (null (fn-cpp-authority *cpp-s1*)) (null (fn-cpp-authority *cpp-s7*))))
(assert-event (equal (fn-cpp-authority *cpp-s8*) 0))

; The exact decision surface the native marker adapter calls.  Its actions,
; terminal outcomes, and every successful phase agree with the full machine.
(assert-event
 (equal (list (fn-cpp-marker-driver-action :marker-staged)
              (fn-cpp-marker-driver-action :marker-data-durable)
              (fn-cpp-marker-driver-action :marker-attempted))
        '(:stage-and-file-barrier :replace :directory-barrier)))
(assert-event
 (equal (fn-cpp-marker-driver-step
         (fn-cpp-marker-driver-step
          (fn-cpp-marker-driver-step :marker-staged :ok) :ok) :ok)
        :idle))
(assert-event (equal (fn-cpp-marker-driver-outcome :idle) :durable))
(assert-event (equal (fn-cpp-marker-driver-outcome :candidate-published) :refused))
(assert-event (equal (fn-cpp-marker-driver-outcome :fenced-marker) :uncertain))
(assert-event
 (equal (fn-cpp-marker-driver-step (fn-cpp-phase *cpp-s5*) :ok)
        (fn-cpp-phase (fn-cpp-marker-step *cpp-s5* :ok))))
; Tooth for the correspondence hypothesis: without statep the full machine
; refuses the forged state while the phase-only driver would advance it.
(defconst *cpp-bad-driver-state* '(:fn-cpp nil 10 :marker-staged nil nil nil))
(assert-event (not (fn-cpp-statep *cpp-bad-driver-state*)))
(assert-event
 (not (equal (fn-cpp-marker-driver-step
              (fn-cpp-phase *cpp-bad-driver-state*) :ok)
             (fn-cpp-phase (fn-cpp-marker-step *cpp-bad-driver-state* :ok)))))

; ACL2 owns the exact on-disk names, both read bounds, canonical parsing, the
; sorted namespace plan, contiguous allocation and exhausted outcomes.
(assert-event
 (equal (fn-cpp-generation-name-chars 0)
        (coerce "generation-0.fncp" 'list)))
(assert-event
 (equal (fn-cpp-generation-name-decode
         (coerce "generation-4294967295.fncp" 'list))
        '(:ok 4294967295)))
(assert-event
 (equal (fn-cpp-namespace-name-decode *fn-cpp-selection-name*)
        '(:selection)))
(assert-event (equal *fn-cpp-selection-read-bound* 47))
;; PRF-171: the old figures are the instance T = 4095 (capacity 4096).
(defconst *cpp-cap* (fn-cpp-generation-capacity 4095))
(assert-event (equal *cpp-cap* 4096))
(assert-event (equal (fn-cpp-namespace-observation-limit *cpp-cap*) 4097))
(assert-event
 (equal (fn-cpp-namespace-plan
         (list (coerce "generation-2.fncp" 'list)
               *fn-cpp-selection-name*
               (coerce "generation-0.fncp" 'list)
               (coerce "generation-1.fncp" 'list))
         *cpp-cap*)
        '(:ok (0 1 2))))
; Canonicality, numeric domain and observation bound are independent teeth.
(assert-event
 (equal (fn-cpp-generation-name-decode
         (coerce "generation-00.fncp" 'list)) '(:error :name)))
(assert-event
 (equal (fn-cpp-generation-name-decode
         (coerce "generation-4294967296.fncp" 'list)) '(:error :name)))
(assert-event
 (equal (fn-cpp-generation-name-decode
         (coerce "generation--1.fncp" 'list)) '(:error :name)))
(assert-event
 (equal (fn-cpp-namespace-plan
         (make-list 4098 :initial-element *fn-cpp-selection-name*)
         *cpp-cap*)
        '(:error :bound)))
(assert-event (equal (fn-cpp-next-generation nil *cpp-cap*) 0))
(assert-event (equal (fn-cpp-next-generation '(0 1 2) *cpp-cap*) 3))
(assert-event (equal (fn-cpp-next-generation '(0 2) *cpp-cap*) :bad))
(assert-event (equal (fn-cpp-next-generation-from nil 4096 *cpp-cap*) :exhausted))
(assert-event (equal (fn-cpp-next-generation-from nil 4294967296 (expt 2 40))
                     :exhausted))

;; fn-cpp-next-generation-refuses-exactly-at-the-profile-capacity: past the
;; old 4,096 under a larger T; at the capacity, exhausted; one below, the next.
(defun cpp-gens (n) (if (zp n) nil (append (cpp-gens (1- n)) (list (1- n)))))
(defconst *cpp-4097* (cpp-gens 4097))
(assert-event (equal (fn-cpp-next-generation *cpp-4097* (fn-cpp-generation-capacity 8191))
                     4097))
(assert-event (equal (fn-cpp-next-generation *cpp-4097* (fn-cpp-generation-capacity 4096))
                     :exhausted))
(assert-event (equal (fn-cpp-next-generation (cpp-gens 4096) *cpp-cap*) :exhausted))
(assert-event (equal (fn-cpp-next-generation (cpp-gens 4095) *cpp-cap*) 4095))
;; Tooth (not :bad): a gapped namespace below the capacity is :bad, not the
;; count.
(assert-event (equal (fn-cpp-next-generation '(0 2) 10) :bad))
(must-fail
 (assert-event (equal (fn-cpp-next-generation '(0 2) 10) (len '(0 2)))))
;; Tooth (capacity within the uint32 width): past it the codec, not the
;; profile, exhausts the numbering.
(assert-event (not (<= (expt 2 40) (+ 1 *fn-cbor-max-uint*))))
(must-fail
 (assert-event (equal (fn-cpp-next-generation-from nil 4294967296 (expt 2 40))
                      (if (<= (expt 2 40) 4294967296) :exhausted 4294967296))))

; The immutable executor receives authority only through this ACL2 gate.
(defconst *cpp-publication* (fn-cpp-publication-initial '(0 1) 2 t t *cpp-cap*))
(assert-event (equal (car *cpp-publication*) :ok))
(assert-event (fn-jpub-statep (car (cdr (cdr *cpp-publication*)))))
(assert-event (fn-jpub-authorityp (car (cdr (cdr *cpp-publication*)))))
; Every premise is a tooth: no exclusive owner, occupied exact name, proposed
; generation mismatch, and a gapped namespace all refuse authorization.
(assert-event (equal (fn-cpp-publication-initial '(0 1) 2 nil t *cpp-cap*)
                     '(:error :authority)))
(assert-event (equal (fn-cpp-publication-initial '(0 1) 2 t nil *cpp-cap*)
                     '(:error :occupied)))
(assert-event (equal (fn-cpp-publication-initial '(0 1) 3 t t *cpp-cap*)
                     '(:error :generation)))
(assert-event (equal (fn-cpp-publication-initial '(0 2) 3 t t *cpp-cap*)
                     '(:error :namespace)))

; A second generation over the longer prefix, selected over the first.
(defconst *cpp-t1* (fn-cpp-stage *cpp-s8* *cpp-prefix-1* 6 *cpp-digest*))
(defconst *cpp-t2* (fn-cpp-candidate-file-result *cpp-t1* :ok))
(defconst *cpp-t3* (fn-cpp-candidate-link-result *cpp-t2* :ok))
(defconst *cpp-t4* (fn-cpp-candidate-dir-result *cpp-t3* :ok))
(defconst *cpp-t5* (fn-cpp-select *cpp-t4*))
(defconst *cpp-t6* (fn-cpp-marker-file-result *cpp-t5* :ok))
(defconst *cpp-t7* (fn-cpp-marker-replace-result *cpp-t6* :ok))
(defconst *cpp-t8* (fn-cpp-marker-dir-result *cpp-t7* :ok))
(assert-event (equal (fn-cpp-phase *cpp-t8*) :idle))
(assert-event (equal (fn-cpp-authority *cpp-t8*) 1))
(assert-event (equal (fn-cpp-authority *cpp-t7*) 0))
(assert-event (equal (len (fn-cpp-generations *cpp-t8*)) 2))
(assert-event (fn-cpp-find 0 (fn-cpp-generations *cpp-t8*)))

; -----------------------------------------------------------------------------
; KEYSTONE 1 and 5: every cut of the second publication yields the old
; authority (0) or the complete new generation (1), never a partial one; the
; old generation is retained throughout.

(defun cpp-recover-name (image)
  (fn-cpp-recover-name (fn-cpp-recover image *cpp-groups* 10 6 2 *cpp-digest*)))

(defun cpp-image-outcome (image)
  (car (fn-cpp-recover image *cpp-groups* 10 6 2 *cpp-digest*)))

; Before the marker phases, every choice recovers generation 0.
(assert-event
 (let ((states (list *cpp-t1* *cpp-t2* *cpp-t3* *cpp-t4* *cpp-t5*)))
   (and (equal (cpp-recover-name (fn-cpp-crash (nth 0 states) :new :present)) 0)
        (equal (cpp-recover-name (fn-cpp-crash (nth 1 states) :new :present)) 0)
        (equal (cpp-recover-name (fn-cpp-crash (nth 2 states) :new :present)) 0)
        (equal (cpp-recover-name (fn-cpp-crash (nth 3 states) :new :present)) 0)
        (equal (cpp-recover-name (fn-cpp-crash (nth 4 states) :new :present)) 0)
        (equal (cpp-recover-name (fn-cpp-crash (nth 2 states) :old :absent)) 0)
        (equal (cpp-image-outcome (fn-cpp-crash (nth 2 states) :old :absent)) :ok))))
; The generation choice is live only in the data-durable window.
(assert-event (null (fn-cpp-find 1 (fn-cpp-image-generations
                                    (fn-cpp-crash *cpp-t1* :old :present)))))
(assert-event (fn-cpp-find 1 (fn-cpp-image-generations
                              (fn-cpp-crash *cpp-t2* :old :present))))
(assert-event (null (fn-cpp-find 1 (fn-cpp-image-generations
                                    (fn-cpp-crash *cpp-t2* :old :absent)))))
(assert-event (fn-cpp-find 1 (fn-cpp-image-generations
                              (fn-cpp-crash *cpp-t4* :old :absent))))
; In the marker phases the :new choice names generation 1 and the image
; holds its complete bytes; recovery yields exactly the second capture.
(assert-event
 (and (equal (fn-cpp-recover (fn-cpp-crash *cpp-t6* :new :absent)
                             *cpp-groups* 10 6 2 *cpp-digest*)
             (list :ok 1 *cpp-cp-1*))
      (equal (fn-cpp-recover (fn-cpp-crash *cpp-t7* :new :absent)
                             *cpp-groups* 10 6 2 *cpp-digest*)
             (list :ok 1 *cpp-cp-1*))
      (equal (fn-cpp-recover (fn-cpp-crash *cpp-t7* :old :absent)
                             *cpp-groups* 10 6 2 *cpp-digest*)
             (list :ok 0 *cpp-cp-0*))
      (equal (fn-cpp-recover (fn-cpp-crash *cpp-t8* :new :present)
                             *cpp-groups* 10 6 2 *cpp-digest*)
             (list :ok 1 *cpp-cp-1*))))
; Teeth for keystone 1: the statep hypothesis.  fn-cpp-crash refuses a
; non-state (it returns the stable image), so the hypothesis cannot be
; dropped through the crash constructor itself; what the invariant rules out
; is exhibited directly.  A raw state in a marker phase whose candidate was
; never published is not a state, and the image such a state would describe
; (marker naming the unpublished candidate) recovers as :missing, so the
; theorem's second disjunct fails for it.
(defconst *cpp-forged*
  (fn-cpp-make *cpp-groups* 10 :marker-attempted 0
               (fn-cpp-candidate *cpp-t7*) (fn-cpp-generations *cpp-s8*)))
(assert-event (not (fn-cpp-statep *cpp-forged*)))
(assert-event (equal (fn-cpp-phase *cpp-forged*) :marker-attempted))
(defconst *cpp-forged-image*
  (fn-cpp-image-make (fn-cpp-entry-name (fn-cpp-candidate *cpp-forged*))
                     (fn-cpp-generations *cpp-forged*)))
(assert-event (not (fn-cpp-imagep *cpp-forged-image* *cpp-groups* 10)))
(assert-event (equal (car (fn-cpp-recover *cpp-forged-image* *cpp-groups* 10 6 2
                                          *cpp-digest*))
                     :missing))
(assert-event (not (or (equal (fn-cpp-image-marker *cpp-forged-image*)
                    (fn-cpp-authority *cpp-forged*))
             (equal (fn-cpp-find (fn-cpp-image-marker *cpp-forged-image*)
                                 (fn-cpp-image-generations *cpp-forged-image*))
                    (fn-cpp-candidate *cpp-forged*)))))
; The choice hypothesis: an unknown choice is the stable image.
(assert-event (equal (fn-cpp-crash *cpp-t7* :maybe :absent)
                     (fn-cpp-image-make 0 (fn-cpp-generations *cpp-t7*))))

; -----------------------------------------------------------------------------
; KEYSTONE 2: recovery of the complete selected generation is its capture.

(defconst *cpp-image-1* (fn-cpp-crash *cpp-t8* :old :absent))
(assert-event (fn-cpp-imagep *cpp-image-1* *cpp-groups* 10))
(assert-event (equal (fn-cpp-recover *cpp-image-1* *cpp-groups* 10 6 2 *cpp-digest*)
                     (list :ok 1 *cpp-cp-1*)))
; Teeth.  Digest hypothesis dropped: the host's digest over the bytes
; disagrees with the trailer, reported as corruption, never :ok.
(assert-event (not (equal (fn-cpp-recover *cpp-image-1* *cpp-groups* 10 6 2
                                (cons 1 (cdr *cpp-digest*)))
                (list :ok 1 *cpp-cp-1*))))
(assert-event (equal (fn-cpp-recover *cpp-image-1* *cpp-groups* 10 6 2
                                     (cons 1 (cdr *cpp-digest*)))
                     (list :corrupt 1 '(:error :integrity))))
; Frontier bound dropped (observed frontier behind the generation's).
(assert-event (not (equal (fn-cpp-recover *cpp-image-1* *cpp-groups* 10 5 2 *cpp-digest*)
                (list :ok 1 *cpp-cp-1*))))
(assert-event (equal (fn-cpp-recover *cpp-image-1* *cpp-groups* 10 5 2 *cpp-digest*)
                     (list :corrupt 1 '(:error :frontier))))
; Count bound dropped.
(assert-event (not (equal (fn-cpp-recover *cpp-image-1* *cpp-groups* 10 6 1 *cpp-digest*)
                (list :ok 1 *cpp-cp-1*))))
; Image well-formedness dropped: the selected entry's bytes are not the
; encoding of its ghost capture.
(defconst *cpp-image-forged*
  (fn-cpp-corrupt *cpp-image-1* 1 (fn-cpp-entry-octets
                                    (fn-cpp-find 0 (fn-cpp-generations *cpp-t8*)))))
(assert-event (not (fn-cpp-imagep *cpp-image-forged* *cpp-groups* 10)))
(assert-event (not (equal (fn-cpp-recover *cpp-image-forged* *cpp-groups* 10 6 2 *cpp-digest*)
                (list :ok 1 *cpp-cp-1*))))
; A marker naming no generation is the fourth, distinct outcome.
(assert-event (equal (car (fn-cpp-recover (fn-cpp-image-make 7 nil)
                                          *cpp-groups* 10 6 2 *cpp-digest*))
                     :missing))
(assert-event (equal (fn-cpp-recover (fn-cpp-image-make nil nil)
                                     *cpp-groups* 10 6 2 *cpp-digest*)
                     '(:none)))

; -----------------------------------------------------------------------------
; KEYSTONE 3: corruption of the selected generation is reported.

(defconst *cpp-garbage* '(70 78 67 80 1 1 0 0 0 1 9))
(assert-event
 (equal (fn-cpp-recover (fn-cpp-corrupt *cpp-image-1* 1 *cpp-garbage*)
                        *cpp-groups* 10 6 2 *cpp-digest*)
        (list :corrupt 1 (fn-cpc-frame-decode *cpp-garbage* *cpp-digest*
                                              *cpp-groups* 10 6 2))))
(assert-event (equal (car (fn-cpp-recover (fn-cpp-corrupt *cpp-image-1* 1 *cpp-garbage*)
                                          *cpp-groups* 10 6 2 *cpp-digest*))
                     :corrupt))
; Not a silent roll-back: generation 0 is intact in that image and is not
; what recovery returns.
(assert-event (fn-cpp-find 0 (fn-cpp-image-generations
                              (fn-cpp-corrupt *cpp-image-1* 1 *cpp-garbage*))))
(assert-event (not (equal (car (fn-cpp-recover (fn-cpp-corrupt *cpp-image-1* 1 *cpp-garbage*)
                                     *cpp-groups* 10 6 2 *cpp-digest*))
                :ok)))
; Teeth.  The marker hypothesis dropped: corrupting the unselected
; generation 0 is invisible (fn-cpp-corrupting-unselected-generation-is-
; invisible), so the :corrupt conclusion fails.
(assert-event (not (equal (car (fn-cpp-recover (fn-cpp-corrupt *cpp-image-1* 0 *cpp-garbage*)
                                     *cpp-groups* 10 6 2 *cpp-digest*))
                :corrupt)))
(assert-event
 (equal (fn-cpp-recover (fn-cpp-corrupt *cpp-image-1* 0 *cpp-garbage*)
                        *cpp-groups* 10 6 2 *cpp-digest*)
        (fn-cpp-recover *cpp-image-1* *cpp-groups* 10 6 2 *cpp-digest*)))
; The refusal hypothesis dropped: bytes the codec accepts are not
; corruption, even if they were written by a "corrupt" step.
(assert-event (not (equal (car (fn-cpp-recover
                      (fn-cpp-corrupt *cpp-image-1* 1
                                      (fn-cpp-entry-octets
                                       (fn-cpp-find 1 (fn-cpp-generations *cpp-t8*))))
                      *cpp-groups* 10 6 2 *cpp-digest*))
                :corrupt)))
; A whole-frame substitution of the older generation's bytes under the newer
; name is refused as well: the header's count bound is the newer image's,
; but the codec's frontier and configuration checks still hold; what fails
; is that the substituted bytes decode to a checkpoint whose frontier and
; sequence are those of generation 0.  They decode: substitution of one
; complete generation for another is the residual the codec cannot detect,
; exactly as specs/checkpoint.md states.
(assert-event (equal (car (fn-cpp-recover *cpp-image-forged* *cpp-groups* 10 6 2
                                          *cpp-digest*))
                     :ok))
(assert-event (equal (fn-cpp-recover-checkpoint
                      (fn-cpp-recover *cpp-image-forged* *cpp-groups* 10 6 2
                                      *cpp-digest*))
                     *cpp-cp-0*))

; -----------------------------------------------------------------------------
; KEYSTONE 4: selected checkpoint plus suffix equals full replay.

(assert-event (fn-checkpoint-admissible-splitp *cpp-groups* 10 *cpp-prefix-0* 3
                                               (list *cpp-r1*) 6))
(defconst *cpp-image-0* (fn-cpp-crash *cpp-s8* :old :absent))
(assert-event
 (equal (fn-checkpoint-restore
         (fn-cpp-recover-checkpoint
          (fn-cpp-recover *cpp-image-0* *cpp-groups* 10 3 1 *cpp-digest*))
         *cpp-groups* 10 (list *cpp-r1*) 6)
        (fn-checkpoint-full-replay *cpp-groups* 10 (list *cpp-r0* *cpp-r1*) 6)))
(assert-event
 (equal (car (fn-checkpoint-restore
              (fn-cpp-recover-checkpoint
               (fn-cpp-recover *cpp-image-0* *cpp-groups* 10 3 1 *cpp-digest*))
              *cpp-groups* 10 (list *cpp-r1*) 6))
        :ok))
; Teeth: the admissibility hypothesis.  A suffix reusing a transaction id
; below the checkpoint's frontier is not an admissible split, and restore
; refuses it while full replay of the same records is a replay fault, so the
; two sides are not equal.
(defconst *cpp-stale*
  (fn-record-make 1 2 2 "<stale@example.invalid>" '(83 13 10)
                  '("fn.test") "cp-pin-stale" "cp-content-stale"
                  "cp-release-stale" 1 841000000))
(assert-event (not (fn-checkpoint-admissible-splitp *cpp-groups* 10 *cpp-prefix-0* 3
                                                    (list *cpp-stale*) 6)))
(assert-event
 (equal (fn-checkpoint-restore
         (fn-cpp-recover-checkpoint
          (fn-cpp-recover *cpp-image-0* *cpp-groups* 10 3 1 *cpp-digest*))
         *cpp-groups* 10 (list *cpp-stale*) 6)
        '(:error :suffix)))
