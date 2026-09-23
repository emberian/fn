; Bind a parsed topic candidate to the existing T10 authorship context.
; A candidate, even with a matching root declaration, is not an admission.
(in-package "ACL2")
(include-book "topic-history-metadata")

(defun fn-th-verified-author-ref (principal keys)
  (declare (xargs :guard t))
  (let ((snapshot (fn-hsig-keyring-snapshot principal keys)))
    (if (and (fn-cbor-octet-listp snapshot)
             (<= (len snapshot) *fn-cbor-max-uint*))
        (list principal (fn-id-subject-of-payload snapshot))
      nil)))

(defun fn-th-root-controller-matchp (metadata author-ref)
  (declare (xargs :guard t))
  (and (equal (fn-th-at 0 metadata) :root)
       (equal (fn-th-at 2 metadata) (fn-th-at 0 author-ref))
       (equal (fn-th-at 3 metadata) (fn-th-at 1 author-ref))))

(defun fn-th-select-verified-source (source principal keys)
  "Offline candidate with its verifier-supplied author and root binding status."
  (declare (xargs :guard t))
  (let ((projection (fn-th-host-inspect-source source))
        (author-ref (fn-th-verified-author-ref principal keys)))
    (if (not (fn-stmt-okp projection)) projection
      (if (not author-ref) (fn-stmt-error :authorship-context)
        (let ((metadata (fn-stmt-value projection)))
          (fn-stmt-ok
           (list metadata author-ref
                 (if (equal (fn-th-at 0 metadata) :root)
                     (if (fn-th-root-controller-matchp metadata author-ref)
                         :controller-matched
                       :controller-mismatch)
                   :not-root))))))))

(defun fn-th-select-accepted-event (event snapshot)
  "Historical candidate only after T10 binds exact source and enrolled keys."
  (declare (xargs :guard t))
  (if (not (fn-hsig-article-event-snapshot-bindsp-v1 event snapshot))
      (fn-stmt-error :unbound-event)
    (let ((enrolled (fn-hsig-keyring-snapshot-value snapshot)))
      (fn-th-select-verified-source
       (fn-stxa-authored-source event) (first enrolled) (second enrolled)))))

(defthm fn-th-selected-root-matches-verified-context
  (implies (and (fn-stmt-okp (fn-th-select-verified-source
                             source principal keys))
                (equal (fn-th-at 2
                         (fn-stmt-value
                          (fn-th-select-verified-source source principal keys)))
                       :controller-matched))
           (let* ((selected (fn-stmt-value
                             (fn-th-select-verified-source source principal keys)))
                  (root (fn-th-at 0 selected))
                  (author (fn-th-at 1 selected)))
             (and (equal (fn-th-at 0 root) :root)
                  (equal (fn-th-at 2 root) (fn-th-at 0 author))
                  (equal (fn-th-at 3 root) (fn-th-at 1 author))
                  (equal author (fn-th-verified-author-ref principal keys)))))
  :hints (("Goal" :in-theory
           (e/d (fn-th-select-verified-source
                 fn-th-root-controller-matchp
                 fn-stmt-ok fn-stmt-okp fn-stmt-value fn-th-at)
                (fn-th-host-inspect-source fn-th-verified-author-ref
                 fn-th-project-source fn-th-project-fields
                 fn-th-project-field fn-th-field-decode fn-th-decode)))))

(defthm fn-th-selected-report-author-is-verified-context
  (implies (and (fn-stmt-okp (fn-th-select-verified-source
                             source principal keys))
                (equal (fn-th-at 0
                         (fn-th-at 0
                          (fn-stmt-value
                           (fn-th-select-verified-source source principal keys))))
                       :report))
           (equal (fn-th-at 1
                   (fn-stmt-value
                    (fn-th-select-verified-source source principal keys)))
                  (fn-th-verified-author-ref principal keys)))
  :hints (("Goal" :in-theory
           (e/d (fn-th-select-verified-source
                 fn-stmt-ok fn-stmt-okp fn-stmt-value fn-th-at)
                (fn-th-host-inspect-source fn-th-verified-author-ref
                 fn-th-project-source fn-th-project-fields
                 fn-th-project-field fn-th-field-decode fn-th-decode)))))

(defthm fn-th-accepted-selection-uses-exact-source-and-snapshot
  (implies (fn-hsig-article-event-snapshot-bindsp-v1 event snapshot)
           (equal (fn-th-select-accepted-event event snapshot)
                  (let ((enrolled (fn-hsig-keyring-snapshot-value snapshot)))
                    (fn-th-select-verified-source
                     (fn-stxa-authored-source event)
                     (first enrolled) (second enrolled)))))
  :hints (("Goal" :in-theory (enable fn-th-select-accepted-event))))

(defthm fn-th-accepted-selection-refuses-unbound-context
  (implies (not (fn-hsig-article-event-snapshot-bindsp-v1 event snapshot))
           (equal (fn-th-select-accepted-event event snapshot)
                  (fn-stmt-error :unbound-event)))
  :hints (("Goal" :in-theory (enable fn-th-select-accepted-event))))

(defthm fn-th-accepted-root-author-is-historical-enrollment
  (implies
   (and (fn-stmt-okp (fn-th-select-accepted-event event snapshot))
        (equal (fn-th-at 2
                 (fn-stmt-value (fn-th-select-accepted-event event snapshot)))
               :controller-matched))
   (let* ((enrolled (fn-hsig-keyring-snapshot-value snapshot))
          (selected (fn-stmt-value
                     (fn-th-select-accepted-event event snapshot)))
          (root (fn-th-at 0 selected))
          (author (fn-th-at 1 selected)))
     (and (fn-hsig-article-event-snapshot-bindsp-v1 event snapshot)
          (equal author (fn-th-verified-author-ref
                         (first enrolled) (second enrolled)))
          (equal (fn-th-at 2 root) (fn-th-at 0 author))
          (equal (fn-th-at 3 root) (fn-th-at 1 author)))))
  :hints (("Goal"
           :use ((:instance fn-th-selected-root-matches-verified-context
                            (source (fn-stxa-authored-source event))
                            (principal
                             (first (fn-hsig-keyring-snapshot-value snapshot)))
                            (keys
                             (second (fn-hsig-keyring-snapshot-value snapshot)))))
           :in-theory (e/d (fn-th-select-accepted-event)
                           (fn-th-select-verified-source
                            fn-th-verified-author-ref
                            fn-th-host-inspect-source)))))
