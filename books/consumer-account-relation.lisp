; Proof-only account publication relation. Never call these traversals on
; a served path: the producer must establish and preserve them incrementally.
; PRF-1140 remains open until stage/replay/owner installation are joined.
(in-package "ACL2")
(include-book "consumer-account-adoption")

(defun fn-caar-credential-descriptor (credential)
  (declare (xargs :guard t))
  (let ((secret (fn-auth-cred-secret credential)))
    (fn-cac-fields-encode
     (list (fn-auth-cred-principal credential)
           (fn-authsec-ver-salt secret) (fn-authsec-ver-digest secret)
           (fn-authsec-ver-stored-key secret) (fn-authsec-ver-server-key secret)
           (if (fn-auth-cred-postingp credential) 1 0))
     '(:bytes32 :bytes16 :bytes32 :bytes32 :bytes32 :flag))))

(defun fn-caar-bindingp (row binding watermark)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-cp-authority-rowp row watermark)
       (fn-cai-namep (fn-cp-nth 1 row) *fn-auth-max-name-octets*)
       (true-listp binding) (equal (len binding) 3)
       (equal (car binding) :account-binding)
       (equal (fn-cp-nth 1 binding) row)
       (let ((credential (fn-cp-nth 2 binding)))
         (if (fn-cp-nth 3 row)
             (and (fn-auth-credp credential)
                  (equal (fn-auth-cred-name credential) (fn-cp-nth 1 row))
                  (equal (fn-cp-nth 4 row)
                         (fn-caar-credential-descriptor credential)))
           (null credential)))))

(defun fn-caar-rowsp (rows index watermark)
  (declare (xargs :guard t :verify-guards nil))
  (if (consp rows)
      (and (fn-caar-bindingp
            (car rows) (fn-cai-get-octets (fn-cp-nth 1 (car rows)) index)
            watermark)
           (or (not (consp (cdr rows)))
               (fn-caa-name-lessp (fn-cp-nth 1 (car rows))
                                  (fn-cp-nth 1 (cadr rows))))
           (fn-caar-rowsp (cdr rows) index watermark))
    (null rows)))

; Rebuild in the producer's insertion order. Equality to this complete
; reconstruction excludes hidden extra keys/branches as well as omissions.
(defun fn-caar-rebuild (rows source acc)
  (declare (xargs :guard t))
  (if (consp rows)
      (fn-caar-rebuild
       (cdr rows) source
       (fn-cai-put-octets (fn-cp-nth 1 (car rows))
                          (fn-cai-get-octets (fn-cp-nth 1 (car rows)) source) acc))
    acc))

(defun fn-caar-index-relp (rows index watermark)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-caar-rowsp rows index watermark)
       (equal index (fn-caar-rebuild rows index nil))))

(defun fn-caar-credentials (rows index)
  (declare (xargs :guard t))
  (if (consp rows)
      (if (fn-cp-nth 3 (car rows))
          (cons (fn-cp-nth 2
                          (fn-cai-get-octets (fn-cp-nth 1 (car rows)) index))
                (fn-caar-credentials (cdr rows) index))
        (fn-caar-credentials (cdr rows) index))
    nil))

(defun fn-caar-root-shapep (root)
  (declare (xargs :guard t))
  (and (true-listp root) (equal (len root) 4)
       (equal (car root) :account-root)
       (natp (fn-cp-nth 1 root)) (<= (fn-cp-nth 1 root) 7)))

(defun fn-caar-root-relp (rows watermark root)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-caar-root-shapep root)
       (fn-caar-index-relp rows (fn-cp-nth 2 root) watermark)
       (equal (fn-cp-nth 3 root)
              (fn-caar-credentials rows (fn-cp-nth 2 root)))))

(defun fn-caar-installed-relp (rows watermark root config)
  (declare (xargs :guard t :verify-guards nil))
  (and (fn-caar-root-relp rows watermark root)
       (equal config (fn-caa-root-auth-config root))))

; The trie already contains every staged row. Credentials are accumulated
; for forward rows only. Moving one reversed head preserves the complete
; row sequence, while adding exactly its live credential to the forward list.
(defun fn-caar-preparation-relp (prep)
  (declare (xargs :guard t :verify-guards nil))
  (let ((reversed (fn-cp-nth 3 prep)) (forward (fn-cp-nth 4 prep))
        (root (fn-cp-nth 5 prep)))
    (and (true-listp prep) (equal (len prep) 8)
         (equal (car prep) :account-preparation)
         (member-eq (fn-cp-nth 1 prep) '(:merge :reverse :ready))
         (true-listp reversed) (true-listp forward)
         (implies (eq (fn-cp-nth 1 prep) :ready) (null reversed))
         (implies (eq (fn-cp-nth 1 prep) :merge) (null forward))
         (fn-caar-root-shapep root)
         (fn-caar-index-relp (revappend reversed forward)
                             (fn-cp-nth 2 root) (fn-cp-nth 7 prep))
         (equal (fn-cp-nth 3 root)
                (fn-caar-credentials forward (fn-cp-nth 2 root))))))

(in-theory (disable fn-caar-credential-descriptor fn-caar-bindingp
                    fn-caar-rowsp fn-caar-rebuild fn-caar-index-relp
                    fn-caar-credentials fn-caar-root-shapep fn-caar-root-relp
                    fn-caar-installed-relp fn-caar-preparation-relp))

(defthm fn-caar-empty-root-establishes-relation
  (implies (and (natp policy) (<= policy 7))
           (fn-caar-root-relp nil watermark (fn-caa-root policy nil nil)))
  :hints (("Goal" :in-theory
           (enable fn-caar-root-relp fn-caar-root-shapep fn-caar-index-relp
                   fn-caar-rowsp fn-caar-rebuild fn-caar-credentials
                   fn-caa-root fn-cp-nth))))

(defthm fn-caar-prepare-preserves-complete-relation
  (implies (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
                (equal (car (fn-caa-prepare s a event)) :ok))
           (fn-caar-preparation-relp
            (fn-cp-nth 5 (fn-cp-nth 5
             (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-prepare s a event)))))))
  :hints (("Goal" :in-theory
           (e/d (fn-caar-preparation-relp fn-caar-root-shapep revappend
                   fn-caar-credentials fn-caa-prepare fn-caa-root
                   fn-caa-preparation fn-caa-pending fn-caa-success
                   fn-caa-authority-pending fn-cp-state-carry fn-cp-nth)
                (revappend-removal fn-cai-get-is-existing-trie-get)))))

(defthm fn-caar-fence-publishes-complete-root
  (implies
   (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
        (equal (fn-cp-nth 4 (fn-cp-nth 5 a))
               (fn-cp-nth 7 (fn-cp-nth 5 (fn-cp-nth 5 a))))
        (equal (car (fn-caa-fence s a event op)) :ok))
   (let* ((one (fn-caa-fence s a event op))
          (authority (fn-cp-nth 6 (fn-cp-nth 1 one))))
     (fn-caar-root-relp (fn-cp-nth 4 authority)
                        (fn-cp-nth 2 authority) (fn-cp-nth 2 one))))
  :hints (("Goal" :in-theory
           (enable fn-caar-preparation-relp fn-caar-root-relp
                   fn-caa-fence fn-caa-success fn-cp-state-carry fn-cp-nth))))

(defthm fn-caar-seal-preserves-complete-relation
  (implies (and (fn-caar-preparation-relp (fn-cp-nth 5 (fn-cp-nth 5 a)))
                (equal (car (fn-caa-seal s a event op)) :ok))
           (fn-caar-preparation-relp
            (fn-cp-nth 5 (fn-cp-nth 5
             (fn-cp-nth 6 (fn-cp-nth 1 (fn-caa-seal s a event op)))))))
  :hints (("Goal" :in-theory
           (e/d (fn-caar-preparation-relp fn-caa-seal fn-caa-preparation
                 fn-caa-pending fn-caa-success fn-caa-authority-pending
                 fn-cp-state-carry fn-cp-nth revappend)
                (revappend-removal)))))

; Proof-only key membership. The public lookup theorem below eliminates
; this intermediate predicate and names actual adopted rows/bindings.
(defun fn-caar-has-namep (name rows)
  (declare (xargs :guard t))
  (if (consp rows)
      (or (equal name (fn-cp-nth 1 (car rows)))
          (fn-caar-has-namep name (cdr rows)))
    nil))

(local
 (defthm fn-caar-lookup-of-rebuild
   (implies (and (fn-caar-rowsp rows source watermark)
                 (fn-cbor-octet-listp name))
            (equal (fn-cai-get-octets name (fn-caar-rebuild rows source acc))
                   (if (fn-caar-has-namep name rows)
                       (fn-cai-get-octets name source)
                     (fn-cai-get-octets name acc))))
   :hints (("Goal" :induct (fn-caar-rebuild rows source acc)
            :in-theory
            (e/d (fn-caar-rebuild fn-caar-rowsp fn-caar-bindingp
                  fn-cai-namep fn-caar-has-namep)
                 (fn-cp-authority-rowp fn-auth-credp fn-cp-nth
                  fn-caa-name-lessp fn-cai-get-is-existing-trie-get
                  fn-cai-put-is-existing-trie-put))))))

(local
 (defthm fn-caar-listed-binding-is-produced
   (implies (and (fn-caar-rowsp rows index watermark)
                 (fn-caar-has-namep name rows))
            (let* ((binding (fn-cai-get-octets name index))
                   (row (fn-cp-nth 1 binding)))
              (and (member-equal row rows)
                   (equal (fn-cp-nth 1 row) name)
                   (fn-caar-bindingp row binding watermark))))
   :hints (("Goal" :induct (fn-caar-has-namep name rows)
            :in-theory
            (e/d (fn-caar-has-namep fn-caar-rowsp fn-caar-bindingp)
                 (fn-cp-authority-rowp fn-auth-credp fn-cp-nth
                  fn-caa-name-lessp fn-cai-get-is-existing-trie-get
                  fn-cai-put-is-existing-trie-put))))))

(local
 (defthm fn-caar-lookup-empty
   (equal (fn-cai-get-octets name nil) nil)
   :hints (("Goal" :in-theory (enable fn-cai-get-is-existing-trie-get)))))

(defthm fn-caar-lookup-belongs-to-adopted-rows
  (implies (and (fn-caar-root-relp rows watermark root)
                (fn-cbor-octet-listp name)
                (fn-cai-get-octets name (fn-cp-nth 2 root)))
           (let* ((binding (fn-cai-get-octets name (fn-cp-nth 2 root)))
                  (row (fn-cp-nth 1 binding)))
             (and (member-equal row rows)
                  (equal (fn-cp-nth 1 row) name)
                  (fn-caar-bindingp row binding watermark))))
  :hints (("Goal"
           :use ((:instance fn-caar-lookup-of-rebuild
                            (source (fn-cp-nth 2 root)) (acc nil))
                 (:instance fn-caar-listed-binding-is-produced
                            (index (fn-cp-nth 2 root))))
           :in-theory
           (e/d (fn-caar-root-relp fn-caar-index-relp)
                (fn-caar-rowsp fn-caar-bindingp fn-caar-has-namep
                 fn-caar-rebuild fn-cp-nth fn-caar-lookup-of-rebuild
                 fn-caar-listed-binding-is-produced
                 fn-cai-get-is-existing-trie-get)))))

; Octet well-formedness is unnecessary for this membership conclusion:
; even malformed query names can only reach a produced binding. Normalize
; only in the proof, matching the actual total key-character operation.
(local
 (defun fn-caar-normalize-name (name)
   (if (consp name)
       (cons (if (fn-cbor-octetp (car name)) (car name) 0)
             (fn-caar-normalize-name (cdr name)))
     nil)))
(local
 (defthm fn-caar-normalized-name-is-octets
   (fn-cbor-octet-listp (fn-caar-normalize-name name))
   :hints (("Goal" :in-theory
            (enable fn-caar-normalize-name fn-cbor-octet-listp fn-cbor-octetp)))))
(local
 (defthm fn-caar-normalized-key-is-original
   (equal (fn-cai-key (fn-caar-normalize-name name)) (fn-cai-key name))
   :hints (("Goal" :in-theory
            (enable fn-caar-normalize-name fn-cai-key fn-cai-key-character
                    fn-cbor-octetp)))))
(local
 (defthm fn-caar-normalized-lookup-is-original
   (equal (fn-cai-get-octets (fn-caar-normalize-name name) index)
          (fn-cai-get-octets name index))
   :hints (("Goal" :in-theory (enable fn-cai-get-is-existing-trie-get)))))

(defthm fn-caar-any-lookup-belongs-to-adopted-rows
  (implies (and (fn-caar-root-relp rows watermark root)
                (fn-cai-get-octets name (fn-cp-nth 2 root)))
           (let* ((binding (fn-cai-get-octets name (fn-cp-nth 2 root)))
                  (row (fn-cp-nth 1 binding)))
             (and (member-equal row rows)
                  (fn-caar-bindingp row binding watermark))))
  :hints (("Goal"
           :use ((:instance fn-caar-lookup-belongs-to-adopted-rows
                            (name (fn-caar-normalize-name name))))
           :in-theory
           (disable fn-caar-root-relp fn-caar-bindingp fn-caar-normalize-name
                    fn-caar-lookup-belongs-to-adopted-rows
                    fn-cai-get-is-existing-trie-get))))

(defthm fn-caar-current-binding-is-adopted-live-account
  (implies (and (fn-caar-root-relp rows watermark root)
                (fn-caa-current-binding name root))
           (let* ((binding (fn-caa-current-binding name root))
                  (row (fn-cp-nth 1 binding)))
             (and (member-equal row rows)
                  (equal (fn-cp-nth 1 row) name)
                  (fn-cp-nth 3 row)
                  (fn-caar-bindingp row binding watermark))))
  :hints (("Goal"
           :use ((:instance fn-caar-lookup-belongs-to-adopted-rows))
           :in-theory
           (e/d (fn-caa-current-binding fn-caa-root-index fn-cai-lookup fn-cai-namep)
                (fn-caar-root-relp fn-caar-bindingp fn-cp-nth
                 fn-caar-lookup-belongs-to-adopted-rows
                 fn-cai-get-is-existing-trie-get)))))
