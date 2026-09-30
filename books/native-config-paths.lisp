; fn.toml paths relative to fn.toml's own directory (row S8, operability
; review drag 10: moving a node).
;
; A path in fn.toml that does not start with `/' names a file under the
; directory fn.toml is in, whatever directory the command runs from; an
; absolute path is taken as written.  The paths are the store, the TLS
; certificate and key, the credential file, the log and the control socket
; (the credential file and control socket default under the store, so they
; follow it).  `[alerts] command' stays absolute: it is a program the node
; runs, refused at load when relative (books/native-config.lisp).
;
; The host observes its working directory and names the fn.toml it was
; given; ACL2 decides the directory (`fn-ncpath-base'), resolves the loaded
; configuration (`fn-ncpath-resolve-config') and hands the operator the
; octets of the resolved configuration (`fn-ncpath-config-octets'), which
; `fn-native-operator-run' then loads as it loads any fn.toml: every verb,
; `run' included, sees absolute paths, and the round trip of the rendering
; (books/native-config-show.lisp fn-native-config-show-round-trip) is what
; makes the octets the resolved configuration.
(in-package "ACL2")
(include-book "native-config")
(include-book "native-config-show")

(defun fn-ncpath-relativep (path)
  (declare (xargs :guard t))
  (and (stringp path) (< 0 (length path))
       (not (equal (char path 0) #\/))))

; A base directory: absolute, and without a trailing `/' unless it is `/'.
(defun fn-ncpath-basep (base)
  (declare (xargs :guard t))
  (fn-ncfg-absolutep base))

(defun fn-ncpath-join (base path)
  (declare (xargs :guard t))
  (if (and (stringp base) (stringp path))
      (if (equal base "/")
          (concatenate 'string "/" path)
        (concatenate 'string base "/" path))
    path))

; PATH resolved under BASE: a relative path joined to it, anything else as
; written.
(defun fn-ncpath-resolve (path base)
  (declare (xargs :guard t))
  (if (and (fn-ncpath-basep base) (fn-ncpath-relativep path))
      (fn-ncpath-join base path)
    path))

(defun fn-ncpath-resolve-config (c base)
  (declare (xargs :guard t))
  ; The constructor leaves the optional cold-resource policy absent. Path
  ; resolution must retain the explicit policy, including its refusal at
  ; the operator boundary, rather than silently resetting it to the default.
  (update-nth 29 (fn-native-config-cold-resources c)
   (fn-native-config-make
   (fn-ncpath-resolve (fn-native-config-store c) base)
   (fn-native-config-listener-host c) (fn-native-config-listener-port c)
   (fn-ncpath-resolve (fn-native-config-tls-cert c) base)
   (fn-ncpath-resolve (fn-native-config-tls-key c) base)
   (fn-native-config-auth-requiredp c) (fn-native-config-auth-protected-onlyp c)
   (fn-ncpath-resolve (fn-native-config-auth-path c) base)
   (fn-native-config-posting-enabledp c) (fn-native-config-posting-agent c)
   (fn-native-config-anchor-server c)
   (fn-ncpath-resolve (fn-native-config-log-path c) base)
   (fn-ncpath-resolve (fn-native-config-control-path c) base)
   (fn-native-config-acl2-path c) (fn-native-config-acl2-slots c)
   (fn-native-config-alerts-command c)
   (fn-native-config-alerts-headroom-min-percent c)
   (fn-native-config-alerts-refusal-rate-per-minute c)
   (fn-native-config-alerts-cooldown-seconds c)
   (fn-native-config-ops-mission c) (fn-native-config-ops-unit c)
   (fn-native-config-ops-scope c) (fn-native-config-ops-keep-releases c)
   (fn-native-config-ops-log-max-bytes c) (fn-native-config-ops-log-keep c)
   (fn-native-config-ops-memory-max c) (fn-native-config-listener-tls-port c))))

; The octets up to (not including) the last `/' of reversed octets REV, or
; nil when there is none.
(defun fn-ncpath-dirname-rev (rev)
  (declare (xargs :guard t))
  (if (consp rev)
      (if (equal (car rev) 47) (cdr rev) (fn-ncpath-dirname-rev (cdr rev)))
    nil))

(defun fn-ncpath-strip-slashes-rev (rev)
  ; Trailing slashes off (reversed: leading), keeping a lone `/'.
  (declare (xargs :guard t))
  (if (and (consp rev) (equal (car rev) 47) (consp (cdr rev)))
      (fn-ncpath-strip-slashes-rev (cdr rev))
    rev))

; The directory fn.toml is in, from the host's working directory CWD and the
; configuration path CONFIG-PATH as it was given (both octet lists): the
; path's directory when it is absolute, else the path's directory under CWD,
; else CWD.  Nil when that is not an absolute printable path.
(defun fn-ncpath-base (cwd config-path)
  (declare (xargs :guard t))
  (let* ((dir-rev (fn-ncpath-dirname-rev (fn-ncfg-reverse config-path)))
         (absolute (and (consp config-path) (equal (car config-path) 47)))
         (octets (cond (absolute (if (consp dir-rev)
                                     (fn-ncfg-reverse dir-rev)
                                   (list 47)))
                       ((consp dir-rev)
                        (let ((top (true-list-fix
                                    (fn-ncfg-reverse
                                     (fn-ncpath-strip-slashes-rev (fn-ncfg-reverse cwd))))))
                          (append (if (equal top (list 47)) nil top)
                                  (list 47) (fn-ncfg-reverse dir-rev))))
                       (t cwd)))
         (octets (fn-ncfg-reverse (fn-ncpath-strip-slashes-rev (fn-ncfg-reverse octets)))))
    (if (and (true-listp octets) (fn-ncfg-printablep octets)
             (fn-ncpath-basep (fn-record-octets-string octets)))
        (fn-record-octets-string octets)
      nil)))

; The octets the operator loads: CONFIG-OCTETS itself when BASE is no base,
; when the loader refuses them (the operator then refuses them by name as
; before) or when no path is relative; else the rendering of the resolved
; configuration, or :bad when a resolved path is past the path bound.
(defun fn-ncpath-config-octets (config-octets base)
  (declare (xargs :guard t))
  (if (not (fn-ncpath-basep base))
      config-octets
    (let ((loaded (fn-native-config-load config-octets)))
      (if (not (equal (car loaded) :accepted))
          config-octets
        (let ((resolved (fn-ncpath-resolve-config (cadr loaded) base)))
          (cond ((equal resolved (cadr loaded)) config-octets)
                ((fn-native-config-show-wfp resolved)
                 (fn-native-config-show-octets resolved))
                (t :bad)))))))

; -----------------------------------------------------------------------------
; Theorems

(defthm fn-ncpath-resolve-keeps-an-absolute-path
  (implies (fn-ncfg-absolutep path)
           (equal (fn-ncpath-resolve path base) path)))

(local (defthm fn-ncpath-car-of-append
  (implies (consp x) (and (consp (append x y)) (equal (car (append x y)) (car x))))
  :hints (("Goal" :in-theory (enable binary-append)))))

(local (defthm fn-ncpath-len-of-append
  (equal (len (append x y)) (+ (len x) (len y)))
  :hints (("Goal" :in-theory (enable binary-append len)))))

(local (defthm fn-ncpath-char0-of-string-append
  (implies (and (stringp a) (stringp b) (< 0 (length a)))
           (equal (char (string-append a b) 0) (char a 0)))
  :hints (("Goal" :in-theory (enable string-append char length)))))

; Every resolved path is absolute.
(defthm fn-ncpath-resolve-is-absolute
  (implies (and (fn-ncpath-basep base) (stringp path) (< 0 (length path)))
           (fn-ncfg-absolutep (fn-ncpath-resolve path base)))
  :hints (("Goal" :in-theory (enable fn-ncpath-resolve fn-ncpath-join
                                     fn-ncpath-basep fn-ncfg-absolutep))))

; A configuration loaded from octets is its own shape (the loader's output
; renders, books/native-config-show.lisp fn-native-config-load-renderable),
; so with no relative path the resolution changes nothing.
(defthm fn-ncpath-resolve-config-without-a-base
  (implies (and (not (fn-ncpath-basep base))
                (fn-ncfg-show-shapep c))
           (equal (fn-ncpath-resolve-config c base) c))
  :hints (("Goal" :in-theory (enable fn-ncfg-show-shapep))))

(local (defthm fn-ncpath-load-accepted-shape
  (implies (equal (car (fn-native-config-load octets)) :accepted)
           (equal (list :accepted (cadr (fn-native-config-load octets)))
                  (fn-native-config-load octets)))
  :hints (("Goal" :in-theory (e/d (fn-native-config-load)
                                  (fn-ncfg-normalize fn-ncfg-parse-lines
                                   fn-ncfg-lines fn-ncfg-listener-refusal))))))

; PRF-1021 KEYSTONE (row S8).  The subject is fn-ncpath-config-octets, which the host
; calls through fn-native-operator-run-at (books/native-operator.lisp) before
; every operator verb.  Over a fn.toml the loader admits and a base, the
; octets it hands on load as exactly the configuration with every relative
; path resolved under the base, unless it answers :bad.
(defthm fn-ncpath-config-octets-load-the-resolved-configuration
  (implies (and (fn-ncpath-basep base)
                (equal (car (fn-native-config-load config-octets)) :accepted)
                (not (equal (fn-ncpath-config-octets config-octets base) :bad)))
           (equal (fn-native-config-load
                   (fn-ncpath-config-octets config-octets base))
                  (list :accepted
                        (fn-ncpath-resolve-config
                         (cadr (fn-native-config-load config-octets)) base))))
  :hints (("Goal" :in-theory (disable fn-ncpath-resolve-config
                                      fn-native-config-show-wfp
                                      fn-native-config-show-octets
                                      fn-native-config-load)
           :cases ((equal (fn-ncpath-resolve-config
                           (cadr (fn-native-config-load config-octets)) base)
                          (cadr (fn-native-config-load config-octets)))))))

; The resolved store is the store resolved (the other path fields alike).
(defthm fn-ncpath-resolve-config-store
  (equal (fn-native-config-store (fn-ncpath-resolve-config c base))
         (fn-ncpath-resolve (fn-native-config-store c) base))
  :hints (("Goal" :in-theory (enable fn-native-config-make))))

(defthm fn-ncpath-resolve-config-cold-resources-by-definition
  (equal (fn-native-config-cold-resources (fn-ncpath-resolve-config c base))
         (fn-native-config-cold-resources c))
  :hints (("Goal" :in-theory (enable fn-native-config-cold-resources
                                     fn-ncfg-nth))))

(in-theory (disable fn-ncpath-resolve fn-ncpath-resolve-config fn-ncpath-base
                    fn-ncpath-config-octets))
