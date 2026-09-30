(in-package "ACL2")
(include-book "../../books/decoded-window-initial-write-domains")
(defmacro piw-updater-full (token)
 `(let* ((o (fn-piw-pwz-begin ,token 301 (create-pgs-digest-state)
                (create-fn-zin-st) nil nil nil)) (trace (cdr o)))
  (and (equal (car o) (fn-pwz-begin ,token 301 (create-pgs-digest-state)
                          (create-fn-zin-st) nil nil nil))
       (equal (fn-piw-register-write-roster trace)
         (append (fn-piw-reset-register-roster 0)
           (list '(19 0) '(11 1) (list 18 (min (len (fn-pwz-dictionary ,token)) 32768)))))
       (fn-piw-register-write-domainp (fn-piw-register-write-roster trace))
       (equal (fn-piw-digest-write-roster trace) (fn-piw-token-digest-inputs ,token 301))
       (fn-piw-digest-write-domainp (fn-piw-digest-write-roster trace)))))
(defthm piw-literal-empty-preset-updater-full-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0)))
  (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
       (piw-updater-full token)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-actual-begin-updater-source-boundary
     (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
     (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
     (win nil) (tab nil) (out nil))
  :in-theory (disable fn-piw-pwz-begin fn-pwz-begin fn-piw-register-write-roster
   fn-piw-digest-write-roster fn-piw-register-write-domainp fn-piw-digest-write-domainp
   fn-piw-token-digest-inputs (:e fn-piw-pwz-begin) (:e fn-pwz-begin)))))
(defthm piw-literal-shipped-preset-updater-full-positive
 (let ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 2220533217)))
  (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
       (piw-updater-full token)))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-actual-begin-updater-source-boundary
     (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 2220533217))
     (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
     (win nil) (tab nil) (out nil))
  :in-theory (disable fn-piw-pwz-begin fn-pwz-begin fn-piw-register-write-roster
   fn-piw-digest-write-roster fn-piw-register-write-domainp fn-piw-digest-write-domainp
   fn-piw-token-digest-inputs (:e fn-piw-pwz-begin) (:e fn-pwz-begin)))))
; Logical profile-removal witness, not a selected off_t executable input.
(defthm piw-literal-remove-selected-native-offset-profile
 (let ((token '(:decoded-window 17 7 100 1208925819614629174706176 120 1024 200 99 93100 0)))
  (and (not (fn-pwz-native-offsetp (cddr token)))
       (not (piw-updater-full token))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-begin-exact-digest-write-roster
     (token '(:decoded-window 17 7 100 1208925819614629174706176 120 1024 200 99 93100 0))
     (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
     (win nil) (tab nil) (out nil))
  :in-theory (disable fn-piw-pwz-begin fn-pwz-begin fn-piw-register-write-roster
   fn-piw-digest-write-roster (:e fn-piw-pwz-begin) (:e fn-pwz-begin)))))
; Separately labelled source-argument mutations, no setter-object tariff.
(defthm piw-literal-register-and-digest-domain-mutations
 (and (fn-piw-register-write-domainp '((18 32768)))
      (not (fn-piw-register-write-domainp '((20 0))))
      (not (fn-piw-register-write-domainp '((18 32769))))
      (not (fn-piw-register-write-domainp '((18 -1))))
      (fn-piw-digest-write-domainp '((update-pgs-dc-total 1152921504606846976)))
      (not (fn-piw-digest-write-domainp '((update-pgs-dc-total 1152921504606846977))))
      (not (fn-piw-digest-write-domainp '((update-pgs-dc-mode :chunk))))
      (not (fn-piw-digest-write-domainp '((update-pgs-dc-capture (1 2 3))))))
 :rule-classes nil)
(defthm piw-literal-full-register-roster-and-sentinel-mutation
 (let* ((token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
        (trace (cdr (fn-piw-pwz-begin token 301 (create-pgs-digest-state)
                        (create-fn-zin-st) nil nil nil)))
        (roster (fn-piw-register-write-roster trace)))
  (and (equal roster '((0 0) (1 0) (2 0) (3 0) (4 0) (5 0) (6 0) (7 0)
                       (8 0) (9 0) (10 0) (11 0) (12 0) (13 0) (14 0)
                       (15 0) (16 0) (17 0) (19 0) (11 1) (18 0)))
       (equal (len roster) 21)
       (not (equal (nth 19 roster) '(11 0)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-begin-exact-register-write-roster
     (token '(:decoded-window 17 7 100 2048 120 1024 200 99 93100 0))
     (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
     (win nil) (tab nil) (out nil))
  :in-theory (disable fn-piw-pwz-begin fn-piw-register-write-roster (:e fn-piw-pwz-begin)))))
(defthm piw-literal-full-digest-roster-and-final-override-positive
 (let* ((token '(:decoded-window 17 7 100 2049 120 1024 200 99 93100 0))
        (trace (cdr (fn-piw-pwz-begin token 301 (create-pgs-digest-state)
                        (create-fn-zin-st) nil nil nil)))
        (roster (fn-piw-digest-write-roster trace)))
  (and (fn-pwz-tokenp token) (fn-pwz-native-offsetp (cddr token))
       (equal roster (fn-piw-token-digest-inputs token 301))
       (equal (len roster) 17)
       (equal (nth 3 roster) '(update-pgs-dc-total 264))
       (equal (nth 15 roster) '(update-pgs-dc-total 257))
       (equal (nth 16 roster) '(update-pgs-dc-end 257))
       (not (equal (nth 15 roster) '(update-pgs-dc-total 264)))))
 :rule-classes nil
 :hints (("Goal" :do-not '(preprocess)
  :use (:instance fn-piw-begin-exact-digest-write-roster
     (token '(:decoded-window 17 7 100 2049 120 1024 200 99 93100 0))
     (incarnation 301) (hash (create-pgs-digest-state)) (zin (create-fn-zin-st))
     (win nil) (tab nil) (out nil))
  :in-theory (disable fn-piw-pwz-begin fn-piw-digest-write-roster (:e fn-piw-pwz-begin)))))
