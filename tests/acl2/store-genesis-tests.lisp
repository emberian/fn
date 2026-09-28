;; Teeth for books/store-genesis (lane format-bump-10): the genesis `init'
;; writes opens as itself at every later open of that profile; each other
;; file is refused by name.
(in-package "ACL2")
(include-book "../../books/store-genesis")
(include-book "../../books/codec-attach")
(include-book "must-fail-checked")

(defconst *gnt-node* (make-list 32 :initial-element 7))
(defconst *gnt-salt* '(1 2 3 4))
(defconst *gnt-revision* '(117 110 107 110 111 119 110))   ; unknown
(defconst *gnt-profile* *fn-bs-profile-development*)

; The record and file for these readings (make-event: a defconst never
; evaluates the digest's attachment).
(make-event
 `(defconst *gnt-g* ',(fn-gen-record-for *gnt-node* *gnt-salt* 1000 *gnt-revision*
                                         *gnt-profile*)))
(make-event
 `(defconst *gnt-file* ',(fn-gen-octets-for *gnt-node* *gnt-salt* 1000 *gnt-revision*
                                            *gnt-profile*)))
(make-event `(defconst *gnt-schema* ',(fn-gen-image-schema-digest)))
(make-event `(defconst *gnt-profile-digest* ',(fn-gen-profile-digest-of *gnt-profile*)))

; The record holds the readings, the salt read big-endian from its octets.
(assert-event (fn-gen-p *gnt-g*))
(assert-event (equal (fn-gen-node *gnt-g*) *gnt-node*))
(assert-event (equal (fn-gen-salt *gnt-g*) 16909060))
(assert-event (equal (fn-gen-created *gnt-g*) 1000))
(assert-event (equal (fn-gen-revision *gnt-g*) *gnt-revision*))
(assert-event (equal (fn-gen-format *gnt-g*) *fn-bs-meta-format-10*))

; fn-gen-open-of-octets-for / fn-gen-open-of-the-genesis-init-writes:
; reachable, the complete antecedent and the conclusion.
(assert-event (equal (fn-gen-schema *gnt-g*) *gnt-schema*))
(assert-event (equal (fn-gen-profile-digest *gnt-g*) *gnt-profile-digest*))
(assert-event (equal (fn-gen-frame *gnt-g*) *gnt-file*))
(make-event `(defconst *gnt-verdict* ',(fn-gen-open *gnt-file* *gnt-profile*)))
(assert-event (equal (car *gnt-verdict*) :genesis))
(assert-event (equal (cadr *gnt-verdict*) *gnt-g*))
(assert-event (equal (caddr *gnt-verdict*) (fn-gen-trailer *gnt-file*)))
(assert-event (equal (len (caddr *gnt-verdict*)) 32))
(assert-event (equal (fn-gen-verdict-salt *gnt-verdict*) 16909060))

; Hypothesis removed (the profile digest): the same file opened under
; another profile (config.json swapped) is refused by name.
(assert-event (not (equal (fn-gen-profile-digest-of *fn-bs-profile-scale*)
                          (fn-gen-profile-digest *gnt-g*))))
(assert-event (equal (fn-gen-open *gnt-file* *fn-bs-profile-scale*)
                     '(:refused :profile-digest)))
(assert-event (equal (fn-gen-refusal-text '(:refused :profile-digest))
                     "open refused reason=profile-digest: config.json is not the profile this store was born with"))

; Hypothesis removed (the schema): a record naming another schema digest.
(defconst *gnt-other-schema*
  (update-nth 3 (make-list 32 :initial-element 9) *gnt-g*))
(assert-event (fn-gen-p *gnt-other-schema*))
(assert-event (not (equal (fn-gen-schema *gnt-other-schema*) *gnt-schema*)))
(make-event `(defconst *gnt-other-schema-file* ',(fn-gen-frame *gnt-other-schema*)))
(assert-event (equal (fn-gen-open *gnt-other-schema-file* *gnt-profile*)
                     '(:refused :schema-digest)))

; Hypothesis removed (the format): a record naming format 9.
(defconst *gnt-format-9* (update-nth 1 *fn-bs-meta-format-9* *gnt-g*))
(assert-event (fn-gen-p *gnt-format-9*))
(make-event `(defconst *gnt-format-9-file* ',(fn-gen-frame *gnt-format-9*)))
(assert-event (equal (fn-gen-open *gnt-format-9-file* *gnt-profile*)
                     '(:refused :genesis-format)))

; Hypothesis removed (fn-gen-p): a node identity of 31 octets writes no file,
; and a 31-octet record's frame is refused as damaged.
(assert-event (null (fn-gen-record-for (make-list 31 :initial-element 7) *gnt-salt* 1000
                                       *gnt-revision* *gnt-profile*)))
(defconst *gnt-short-node* (update-nth 2 (make-list 31 :initial-element 7) *gnt-g*))
(assert-event (not (fn-gen-p *gnt-short-node*)))
(make-event
 `(defconst *gnt-short-node-file*
    ',(fn-frame-seal *fn-lg-magic* *fn-lg-version* *fn-gen-kind*
                     (append *fn-lg-genesis*
                             (fn-frame-fields-octets *fn-gen-spec* *gnt-short-node*)))))
(assert-event (equal (fn-gen-open *gnt-short-node-file* *gnt-profile*)
                     '(:refused :genesis-damaged)))
(must-fail-checked
 (thm (implies (equal g *gnt-short-node*)
               (equal (fn-gen-decode (fn-gen-frame g)) g))))

; CORRUPTED-state witness: one octet of the file flipped fails its trailer.
(defconst *gnt-flipped* (update-nth 40 (logxor 1 (nth 40 *gnt-file*)) *gnt-file*))
(assert-event (equal (fn-gen-open *gnt-flipped* *gnt-profile*) '(:refused :genesis-damaged)))
; A record entry (kind 1) of the log is no genesis: the kinds never meet.
(make-event `(defconst *gnt-record-entry* ',(fn-lg-frame *fn-lg-genesis* (list '(1 2 3)))))
(assert-event (equal (fn-gen-open *gnt-record-entry* *gnt-profile*) '(:refused :genesis-damaged)))
; A salt that is not four octets writes no file.
(assert-event (null (fn-gen-octets-for *gnt-node* '(1 2 3) 1000 *gnt-revision* *gnt-profile*)))
