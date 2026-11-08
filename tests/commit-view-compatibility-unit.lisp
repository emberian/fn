; Frozen pre-migration theorem surface, exported from the checked world at
; 11b28d99e (all baseline statements unchanged from 5ee4da987).
; These tests retain the old names/statements without exporting an invariant
; by callee rewrite matrix from the production proof. Every proof uses only
; producer footprints and generic view projection; no producer body is opened.
(in-package "ACL2")
(include-book "../books/commit-durable-all")
(include-book "std/testing/must-fail" :dir :system)

(defthm UPDATE-FN2-CORE-CONTROL-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm UPDATE-FN2-CORE-CONTROL-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (UPDATE-FN2-CORE-CONTROL FN2-CONTROL FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-CORE-STOP-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-CORE-STOP REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-CORE-STOP-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-CORE-STOP REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-CORE-STOP-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (FN2-CORE-STOP REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-CORE-STOP-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (FN2-CORE-STOP REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-CORE-STOP-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (FN2-CORE-STOP REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-CORE-STOP-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (FN2-CORE-STOP REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-CORE-STOP-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (FN2-CORE-STOP REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-CORE-STOP-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                                            (FN2-CORE-STOP REASON FN2-CORE))
                                       (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-CORE-STOP-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (FN2-CORE-STOP REASON FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-MACHINE-REFUSE-WRITE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-MACHINE-REFUSE-WRITE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (FN2-MACHINE-REFUSE-WRITE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (FN2-MACHINE-REFUSE-WRITE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (FN2-MACHINE-REFUSE-WRITE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (FN2-MACHINE-REFUSE-WRITE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (FN2-MACHINE-REFUSE-WRITE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (FN2-MACHINE-REFUSE-WRITE FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-MACHINE-REFUSE-WRITE-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (FN2-MACHINE-REFUSE-WRITE FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-MACHINE-FINISH-FN2-ENV-EK
  (IMPLIES
       (FN2-ENV-EK FN2-CORE FN2-REL-C0)
       (FN2-ENV-EK
            (MV-NTH '4
                    (FN2-MACHINE-FINISH ID BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
            FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-MACHINE-FINISH-FN2-ENV-RK
  (IMPLIES
       (FN2-ENV-RK FN2-CORE FN2-REL-C0)
       (FN2-ENV-RK
            (MV-NTH '4
                    (FN2-MACHINE-FINISH ID BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
            FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-MACHINE-FINISH-FN2-ENV-FK
  (IMPLIES
       (FN2-ENV-FK FN2-CORE FN2-REL-C0)
       (FN2-ENV-FK
            (MV-NTH '4
                    (FN2-MACHINE-FINISH ID BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
            FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-MACHINE-FINISH-FN2-ENV-DK
  (IMPLIES
       (FN2-ENV-DK FN2-CORE FN2-REL-C0)
       (FN2-ENV-DK
            (MV-NTH '4
                    (FN2-MACHINE-FINISH ID BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
            FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-MACHINE-FINISH-KEEPS-COMMIT-IO
  (EQUAL
      (NTH '30
           (MV-NTH '4
                   (FN2-MACHINE-FINISH ID BYTES
                                       STEPS DESCRIPTORS RUNNABLE FN2-CORE)))
      (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-MACHINE-FINISH-KEEPS-COMMIT-ROOT
  (EQUAL
      (NTH '31
           (MV-NTH '4
                   (FN2-MACHINE-FINISH ID BYTES
                                       STEPS DESCRIPTORS RUNNABLE FN2-CORE)))
      (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-MACHINE-REFUSE-PHASE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (MV-NTH '4
                                   (FN2-MACHINE-REFUSE-PHASE ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-MACHINE-REFUSE-PHASE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (MV-NTH '4
                                   (FN2-MACHINE-REFUSE-PHASE ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-MACHINE-REFUSE-PHASE-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (MV-NTH '4
                                   (FN2-MACHINE-REFUSE-PHASE ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-MACHINE-REFUSE-PHASE-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (MV-NTH '4
                                   (FN2-MACHINE-REFUSE-PHASE ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-MACHINE-REFUSE-PHASE-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (MV-NTH '4
                          (FN2-MACHINE-REFUSE-PHASE ID FN2-CORE)))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-MACHINE-REFUSE-PHASE-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (MV-NTH '4
                          (FN2-MACHINE-REFUSE-PHASE ID FN2-CORE)))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-ROOT-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
           (FN2-ENV-EK (UPDATE-FN2-CORE-COMMIT-ROOT FN2-COMMIT-ROOT FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-ROOT-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
           (FN2-ENV-TK (UPDATE-FN2-CORE-COMMIT-ROOT FN2-COMMIT-ROOT FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-ROOT-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
           (FN2-ENV-SK (UPDATE-FN2-CORE-COMMIT-ROOT FN2-COMMIT-ROOT FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-ROOT-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
           (FN2-ENV-OK (UPDATE-FN2-CORE-COMMIT-ROOT FN2-COMMIT-ROOT FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-ROOT-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
           (FN2-ENV-FK (UPDATE-FN2-CORE-COMMIT-ROOT FN2-COMMIT-ROOT FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-ROOT-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
           (FN2-ENV-DK (UPDATE-FN2-CORE-COMMIT-ROOT FN2-COMMIT-ROOT FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-ROOT-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (UPDATE-FN2-CORE-COMMIT-ROOT FN2-COMMIT-ROOT FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-END-ABORT-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-END-ABORT ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-COMMIT-TABLE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-COMMIT-TABLE FN2-COMMIT FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-COMMIT-TABLE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-COMMIT-TABLE FN2-COMMIT FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-COMMIT-TABLE-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (UPDATE-FN2-COMMIT-TABLE FN2-COMMIT FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-COMMIT-TABLE-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (UPDATE-FN2-COMMIT-TABLE FN2-COMMIT FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm UPDATE-FN2-COMMIT-TABLE-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (UPDATE-FN2-COMMIT-TABLE FN2-COMMIT FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-STAGE-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+CB-STAGE ID FN2-ARMS-W-PHASE
                                                FN2-ARMS-W-CB-STAGE FN2-CORE)
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-SETTLED-FN2-ENV-EK
  (IMPLIES
     (FN2-ENV-EK FN2-CORE FN2-REL-C0)
     (FN2-ENV-EK (UPDATE-FN2-CORE-COMMIT-SETTLED FN2-COMMIT-SETTLED FN2-CORE)
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-SETTLED-FN2-ENV-RK
  (IMPLIES
     (FN2-ENV-RK FN2-CORE FN2-REL-C0)
     (FN2-ENV-RK (UPDATE-FN2-CORE-COMMIT-SETTLED FN2-COMMIT-SETTLED FN2-CORE)
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-SETTLED-FN2-ENV-TK
  (IMPLIES
     (FN2-ENV-TK FN2-CORE FN2-REL-C0)
     (FN2-ENV-TK (UPDATE-FN2-CORE-COMMIT-SETTLED FN2-COMMIT-SETTLED FN2-CORE)
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-SETTLED-FN2-ENV-SK
  (IMPLIES
     (FN2-ENV-SK FN2-CORE FN2-REL-C0)
     (FN2-ENV-SK (UPDATE-FN2-CORE-COMMIT-SETTLED FN2-COMMIT-SETTLED FN2-CORE)
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-SETTLED-FN2-ENV-OK
  (IMPLIES
     (FN2-ENV-OK FN2-CORE FN2-REL-C0)
     (FN2-ENV-OK (UPDATE-FN2-CORE-COMMIT-SETTLED FN2-COMMIT-SETTLED FN2-CORE)
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-SETTLE-ROW-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK
      (MV-NTH '1
              (FN2-COMMIT-SETTLE-ROW SETTLED BATCH
                                     EVENT OUTCOME PHASE PUBLISHED FN2-CORE))
      FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SETTLE-ROW-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK
      (MV-NTH '1
              (FN2-COMMIT-SETTLE-ROW SETTLED BATCH
                                     EVENT OUTCOME PHASE PUBLISHED FN2-CORE))
      FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-SCHED-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-SCHED FN2-SCHED FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-SCHED-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-SCHED FN2-SCHED FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-SCHED-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (UPDATE-FN2-CORE-SCHED FN2-SCHED FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-SCHED-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (UPDATE-FN2-CORE-SCHED FN2-SCHED FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-SCHED-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (UPDATE-FN2-CORE-SCHED FN2-SCHED FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-WAKE-OWNER-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WAKE-OWNER OKIND OSLOT OGEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WAKE-OWNER-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WAKE-OWNER OKIND OSLOT OGEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SETTLE-MEMBER-FN2-ENV-EK
  (IMPLIES
       (FN2-ENV-EK FN2-CORE FN2-REL-C0)
       (FN2-ENV-EK (FN2-COMMIT-SETTLE-MEMBER ID M OUTCOME PUBLISHED FN2-CORE)
                   FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SETTLE-MEMBER-FN2-ENV-RK
  (IMPLIES
       (FN2-ENV-RK FN2-CORE FN2-REL-C0)
       (FN2-ENV-RK (FN2-COMMIT-SETTLE-MEMBER ID M OUTCOME PUBLISHED FN2-CORE)
                   FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+CB-CURSOR-FN2-ENV-EK
  (IMPLIES
    (FN2-ENV-EK FN2-CORE FN2-REL-C0)
    (FN2-ENV-EK (FN2-COMMIT-WRITE+CB-CURSOR ID FN2-ARMS-W-CB-CURSOR FN2-CORE)
                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+CB-CURSOR-FN2-ENV-RK
  (IMPLIES
    (FN2-ENV-RK FN2-CORE FN2-REL-C0)
    (FN2-ENV-RK (FN2-COMMIT-WRITE+CB-CURSOR ID FN2-ARMS-W-CB-CURSOR FN2-CORE)
                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-SUCCESSOR-DROP-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (MV-NTH '1
                                   (FN2-SUCCESSOR-DROP BATCH FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm UPDATE-FN2-CORE-EXTENTS-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (UPDATE-FN2-CORE-EXTENTS FN2-EXTENTS FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm UPDATE-FN2-CORE-ALLOC-EDGES-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
           (FN2-ENV-EK (UPDATE-FN2-CORE-ALLOC-EDGES FN2-ALLOC-EDGES FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-ALLOC-EDGES-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
           (FN2-ENV-RK (UPDATE-FN2-CORE-ALLOC-EDGES FN2-ALLOC-EDGES FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-ALLOC-EDGES-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
           (FN2-ENV-FK (UPDATE-FN2-CORE-ALLOC-EDGES FN2-ALLOC-EDGES FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm UPDATE-FN2-CORE-ALLOC-EDGES-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
           (FN2-ENV-DK (UPDATE-FN2-CORE-ALLOC-EDGES FN2-ALLOC-EDGES FN2-CORE)
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm UPDATE-FN2-CORE-ALLOC-EDGES-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (UPDATE-FN2-CORE-ALLOC-EDGES FN2-ALLOC-EDGES FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-UNPREPARE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (MV-NTH '1
                                   (FN2-COMMIT-UNPREPARE ID EDGE FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+CB-STAGE-FN2-ENV-EK
  (IMPLIES
      (FN2-ENV-EK FN2-CORE FN2-REL-C0)
      (FN2-ENV-EK (FN2-COMMIT-WRITE+CB-STAGE ID FN2-ARMS-W-CB-STAGE FN2-CORE)
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+CB-STAGE-FN2-ENV-RK
  (IMPLIES
      (FN2-ENV-RK FN2-CORE FN2-REL-C0)
      (FN2-ENV-RK (FN2-COMMIT-WRITE+CB-STAGE ID FN2-ARMS-W-CB-STAGE FN2-CORE)
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RUN-DROPPING-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
            (FN2-ENV-RK (MV-NTH '4
                                (FN2-COMMIT-RUN-DROPPING ID BUDGET FN2-CORE))
                        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-POOL-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-POOL FN2-POOL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-POOL-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-POOL FN2-POOL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-POOL-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (UPDATE-FN2-CORE-POOL FN2-POOL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-POOL-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (UPDATE-FN2-CORE-POOL FN2-POOL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-POOL-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (UPDATE-FN2-CORE-POOL FN2-POOL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-CORE-POOL-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (UPDATE-FN2-CORE-POOL FN2-POOL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm UPDATE-FN2-CORE-POOL-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (UPDATE-FN2-CORE-POOL FN2-POOL FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-CORE-RELEASE-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK (MV-NTH '1
                       (FN2-CORE-RELEASE SLOT GEN OKIND OSLOT OGEN FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-CORE-RELEASE-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK (MV-NTH '1
                       (FN2-CORE-RELEASE SLOT GEN OKIND OSLOT OGEN FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-CORE-RELEASE-FN2-ENV-TK
  (IMPLIES
   (FN2-ENV-TK FN2-CORE FN2-REL-C0)
   (FN2-ENV-TK (MV-NTH '1
                       (FN2-CORE-RELEASE SLOT GEN OKIND OSLOT OGEN FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-CORE-RELEASE-FN2-ENV-SK
  (IMPLIES
   (FN2-ENV-SK FN2-CORE FN2-REL-C0)
   (FN2-ENV-SK (MV-NTH '1
                       (FN2-CORE-RELEASE SLOT GEN OKIND OSLOT OGEN FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-CORE-RELEASE-FN2-ENV-OK
  (IMPLIES
   (FN2-ENV-OK FN2-CORE FN2-REL-C0)
   (FN2-ENV-OK (MV-NTH '1
                       (FN2-CORE-RELEASE SLOT GEN OKIND OSLOT OGEN FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-IO-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-COMMIT-IO FN2-COMMIT-IO FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-IO-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (UPDATE-FN2-CORE-COMMIT-IO FN2-COMMIT-IO FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-IO-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (UPDATE-FN2-CORE-COMMIT-IO FN2-COMMIT-IO FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-IO-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (UPDATE-FN2-CORE-COMMIT-IO FN2-COMMIT-IO FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-IO-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (UPDATE-FN2-CORE-COMMIT-IO FN2-COMMIT-IO FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-IO-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (UPDATE-FN2-CORE-COMMIT-IO FN2-COMMIT-IO FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOL-FN2-ENV-EK
  (IMPLIES
    (FN2-ENV-EK FN2-CORE FN2-REL-C0)
    (FN2-ENV-EK (MV-NTH '1
                        (FN2-COMMIT-RELEASE-POOL ID ROLE OWNER-GEN FN2-CORE))
                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOL-FN2-ENV-RK
  (IMPLIES
    (FN2-ENV-RK FN2-CORE FN2-REL-C0)
    (FN2-ENV-RK (MV-NTH '1
                        (FN2-COMMIT-RELEASE-POOL ID ROLE OWNER-GEN FN2-CORE))
                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOL-FN2-ENV-TK
  (IMPLIES
    (FN2-ENV-TK FN2-CORE FN2-REL-C0)
    (FN2-ENV-TK (MV-NTH '1
                        (FN2-COMMIT-RELEASE-POOL ID ROLE OWNER-GEN FN2-CORE))
                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOL-FN2-ENV-SK
  (IMPLIES
    (FN2-ENV-SK FN2-CORE FN2-REL-C0)
    (FN2-ENV-SK (MV-NTH '1
                        (FN2-COMMIT-RELEASE-POOL ID ROLE OWNER-GEN FN2-CORE))
                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOL-FN2-ENV-OK
  (IMPLIES
    (FN2-ENV-OK FN2-CORE FN2-REL-C0)
    (FN2-ENV-OK (MV-NTH '1
                        (FN2-COMMIT-RELEASE-POOL ID ROLE OWNER-GEN FN2-CORE))
                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+STOPPED+CB-STAGE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PHASE+STOPPED+CB-STAGE
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-STOPPED
                                FN2-ARMS-W-CB-STAGE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+STOPPED-FN2-ENV-EK
  (IMPLIES
        (FN2-ENV-EK FN2-CORE FN2-REL-C0)
        (FN2-ENV-EK (FN2-COMMIT-WRITE+STOPPED ID FN2-ARMS-W-STOPPED FN2-CORE)
                    FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE
                                FN2-ARMS-W-STOPPED FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE
                                FN2-ARMS-W-STOPPED FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE
                                FN2-ARMS-W-STOPPED FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE
                                FN2-ARMS-W-STOPPED FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON
                       ID FN2-ARMS-W-PHASE
                       FN2-ARMS-W-STOPPED FN2-ARMS-W-CB-CURSOR
                       FN2-ARMS-W-CB-FAILED
                       FN2-ARMS-W-CB-REASON FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (FN2-COMMIT-WRITE+PHASE+STOPPED+CB-CURSOR+CB-FAILED+CB-REASON
                       ID FN2-ARMS-W-PHASE
                       FN2-ARMS-W-STOPPED FN2-ARMS-W-CB-CURSOR
                       FN2-ARMS-W-CB-FAILED
                       FN2-ARMS-W-CB-REASON FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-SUB-DRAIN-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (MV-NTH '4
                                   (FN2-COMMIT-SUB-DRAIN ID BUDGET FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-RUN-UNCERTAIN-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
           (FN2-ENV-EK (MV-NTH '4
                               (FN2-COMMIT-RUN-UNCERTAIN ID BUDGET FN2-CORE))
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-RUN-DRAINING-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
            (FN2-ENV-EK (MV-NTH '4
                                (FN2-COMMIT-RUN-DRAINING ID BUDGET FN2-CORE))
                        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-ROOT-SWAP-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (MV-NTH '1
                          (FN2-COMMIT-ROOT-SWAP ID PUBLISH FN2-CORE)))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-SUCCESSOR-PUBLISH-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (MV-NTH '1
                          (FN2-SUCCESSOR-PUBLISH BATCH FN2-CORE)))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-SUCCESSOR-PUBLISH-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (MV-NTH '1
                          (FN2-SUCCESSOR-PUBLISH BATCH FN2-CORE)))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-STREAM-WAKE-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (MV-NTH '1
                          (FN2-COMMIT-STREAM-WAKE BATCH FN2-CORE)))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-STREAM-WAKE-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (MV-NTH '1
                          (FN2-COMMIT-STREAM-WAKE BATCH FN2-CORE)))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-PUBLISHED-KEEPS-COMMIT-IO
  (EQUAL
   (NTH
      '30
      (FN2-COMMIT-WRITE+PHASE+CB-PUBLISHED ID FN2-ARMS-W-PHASE
                                           FN2-ARMS-W-CB-PUBLISHED FN2-CORE))
   (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-PUBLISHED-KEEPS-COMMIT-ROOT
  (EQUAL
   (NTH
      '31
      (FN2-COMMIT-WRITE+PHASE+CB-PUBLISHED ID FN2-ARMS-W-PHASE
                                           FN2-ARMS-W-CB-PUBLISHED FN2-CORE))
   (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-CB-REASON FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON
                       ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-CURSOR
                       FN2-ARMS-W-CB-FAILED
                       FN2-ARMS-W-CB-REASON FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (FN2-COMMIT-WRITE+PHASE+CB-CURSOR+CB-FAILED+CB-REASON
                       ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-CURSOR
                       FN2-ARMS-W-CB-FAILED
                       FN2-ARMS-W-CB-REASON FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-RUN-PUBLISH-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (MV-NTH '4
                          (FN2-COMMIT-RUN-PUBLISH ID BUDGET FN2-CORE)))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-ROOT-EDGE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
              (FN2-ENV-RK (MV-NTH '1
                                  (FN2-COMMIT-ROOT-EDGE ID INSTALL FN2-CORE))
                          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-ROOT-EDGE-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (MV-NTH '1
                          (FN2-COMMIT-ROOT-EDGE ID INSTALL FN2-CORE)))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (FN2-COMMIT-WRITE+PHASE ID FN2-ARMS-W-PHASE FN2-CORE))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE-KEEPS-COMMIT-ROOT
  (EQUAL (NTH '31
                  (FN2-COMMIT-WRITE+PHASE ID FN2-ARMS-W-PHASE FN2-CORE))
             (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-COMMIT-ALLOCATE-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (MV-NTH '1
                          (FN2-COMMIT-ALLOCATE ID FN2-CORE)))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-COMMIT-RUN-DURABLE-KEEPS-COMMIT-IO
  (EQUAL (NTH '30
                  (MV-NTH '4
                          (FN2-COMMIT-RUN-DURABLE ID BUDGET FN2-CORE)))
             (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm UPDATE-FN2-CORE-OPS-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-OPS FN2-OPS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-OPS-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-OPS FN2-OPS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-OPS-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (UPDATE-FN2-CORE-OPS FN2-OPS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm UPDATE-FN2-CORE-OPS-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (UPDATE-FN2-CORE-OPS FN2-OPS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-ISSUE-WRITE-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK (MV-NTH '3
                       (FN2-ISSUE-WRITE OFFSET SLOT GEN OFF LEN FUA
                                        OKIND OSLOT OGEN PRINCIPAL FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-ISSUE-WRITE-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK (MV-NTH '3
                       (FN2-ISSUE-WRITE OFFSET SLOT GEN OFF LEN FUA
                                        OKIND OSLOT OGEN PRINCIPAL FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-ISSUE-WRITE-FN2-ENV-FK
  (IMPLIES
   (FN2-ENV-FK FN2-CORE FN2-REL-C0)
   (FN2-ENV-FK (MV-NTH '3
                       (FN2-ISSUE-WRITE OFFSET SLOT GEN OFF LEN FUA
                                        OKIND OSLOT OGEN PRINCIPAL FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-ISSUE-WRITE-FN2-ENV-DK
  (IMPLIES
   (FN2-ENV-DK FN2-CORE FN2-REL-C0)
   (FN2-ENV-DK (MV-NTH '3
                       (FN2-ISSUE-WRITE OFFSET SLOT GEN OFF LEN FUA
                                        OKIND OSLOT OGEN PRINCIPAL FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-IO-EDGE-FN2-ENV-EK
  (IMPLIES
         (FN2-ENV-EK FN2-CORE FN2-REL-C0)
         (FN2-ENV-EK
              (MV-NTH '1
                      (FN2-COMMIT-IO-EDGE ID ROLE ADD OPSLOT OPGEN FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-IO-EDGE-FN2-ENV-RK
  (IMPLIES
         (FN2-ENV-RK FN2-CORE FN2-REL-C0)
         (FN2-ENV-RK
              (MV-NTH '1
                      (FN2-COMMIT-IO-EDGE ID ROLE ADD OPSLOT OPGEN FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-IO-EDGE-FN2-ENV-FK
  (IMPLIES
         (FN2-ENV-FK FN2-CORE FN2-REL-C0)
         (FN2-ENV-FK
              (MV-NTH '1
                      (FN2-COMMIT-IO-EDGE ID ROLE ADD OPSLOT OPGEN FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-COMMIT-IO-EDGE-FN2-ENV-DK
  (IMPLIES
         (FN2-ENV-DK FN2-CORE FN2-REL-C0)
         (FN2-ENV-DK
              (MV-NTH '1
                      (FN2-COMMIT-IO-EDGE ID ROLE ADD OPSLOT OPGEN FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE
                                ID
                                FN2-ARMS-W-PENDING FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-WROTE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE
                                ID
                                FN2-ARMS-W-PENDING FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-WROTE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE
                                ID
                                FN2-ARMS-W-PENDING FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-WROTE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (FN2-COMMIT-WRITE+PENDING+CB-ISSUED+CB-WROTE
                                ID
                                FN2-ARMS-W-PENDING FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-WROTE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-LOG-OK-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-LOG-OK
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-DONE FN2-ARMS-W-CB-BYTES
                                FN2-ARMS-W-CB-LOG-OK FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-LOG-OK-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-LOG-OK
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-DONE FN2-ARMS-W-CB-BYTES
                                FN2-ARMS-W-CB-LOG-OK FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RUN-LOG-WRITE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
           (FN2-ENV-EK (MV-NTH '4
                               (FN2-COMMIT-RUN-LOG-WRITE ID BUDGET FN2-CORE))
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-RUN-LOG-WRITE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
           (FN2-ENV-RK (MV-NTH '4
                               (FN2-COMMIT-RUN-LOG-WRITE ID BUDGET FN2-CORE))
                       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-DEPS-OK+CB-LOG-OK-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-DEPS-OK+CB-LOG-OK
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-DONE FN2-ARMS-W-CB-BYTES
                                FN2-ARMS-W-CB-DEPS-OK
                                FN2-ARMS-W-CB-LOG-OK FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-DEPS-OK+CB-LOG-OK-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+CB-ISSUED+CB-DONE+CB-BYTES+CB-DEPS-OK+CB-LOG-OK
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-ISSUED
                                FN2-ARMS-W-CB-DONE FN2-ARMS-W-CB-BYTES
                                FN2-ARMS-W-CB-DEPS-OK
                                FN2-ARMS-W-CB-LOG-OK FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-MARK-ABORT-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-MARK-ABORT BATCH FIRST FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-MARK-ABORT-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-MARK-ABORT BATCH FIRST FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-MARK-ABORT-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (FN2-COMMIT-MARK-ABORT BATCH FIRST FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-COMMIT-MARK-ABORT-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (FN2-COMMIT-MARK-ABORT BATCH FIRST FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-STAGE
                                FN2-ARMS-W-CB-CURSOR FN2-ARMS-W-OUTCOME
                                FN2-ARMS-W-CB-OPEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-STAGE
                                FN2-ARMS-W-CB-CURSOR FN2-ARMS-W-OUTCOME
                                FN2-ARMS-W-CB-OPEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN-FN2-ENV-FK
  (IMPLIES (FN2-ENV-FK FN2-CORE FN2-REL-C0)
               (FN2-ENV-FK (FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-STAGE
                                FN2-ARMS-W-CB-CURSOR FN2-ARMS-W-OUTCOME
                                FN2-ARMS-W-CB-OPEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN-FN2-ENV-DK
  (IMPLIES (FN2-ENV-DK FN2-CORE FN2-REL-C0)
               (FN2-ENV-DK (FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-CURSOR+OUTCOME+CB-OPEN
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-STAGE
                                FN2-ARMS-W-CB-CURSOR FN2-ARMS-W-OUTCOME
                                FN2-ARMS-W-CB-OPEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-COMMIT-RUN-DEPENDENCIES-FN2-ENV-EK
  (IMPLIES
        (FN2-ENV-EK FN2-CORE FN2-REL-C0)
        (FN2-ENV-EK (MV-NTH '4
                            (FN2-COMMIT-RUN-DEPENDENCIES ID BUDGET FN2-CORE))
                    FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-RUN-DEPENDENCIES-FN2-ENV-RK
  (IMPLIES
        (FN2-ENV-RK FN2-CORE FN2-REL-C0)
        (FN2-ENV-RK (MV-NTH '4
                            (FN2-COMMIT-RUN-DEPENDENCIES ID BUDGET FN2-CORE))
                    FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SEAL-SIZE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-SEAL-SIZE ID SIZE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SEAL-SIZE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-SEAL-SIZE ID SIZE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-CORE-WRITE-FN2-ENV-EK
  (IMPLIES
        (FN2-ENV-EK FN2-CORE FN2-REL-C0)
        (FN2-ENV-EK
             (MV-NTH '1
                     (FN2-CORE-WRITE SLOT
                                     GEN IDX BYTE OKIND OSLOT OGEN FN2-CORE))
             FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-CORE-WRITE-FN2-ENV-RK
  (IMPLIES
        (FN2-ENV-RK FN2-CORE FN2-REL-C0)
        (FN2-ENV-RK
             (MV-NTH '1
                     (FN2-CORE-WRITE SLOT
                                     GEN IDX BYTE OKIND OSLOT OGEN FN2-CORE))
             FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-COPY-BYTES-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK
       (MV-NTH '1
               (FN2-COMMIT-COPY-BYTES LEFT SRC SG OFF FROM FG
                                      AT FROM-ID FROM-OGEN ID OGEN FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-COPY-BYTES-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK
       (MV-NTH '1
               (FN2-COMMIT-COPY-BYTES LEFT SRC SG OFF FROM FG
                                      AT FROM-ID FROM-OGEN ID OGEN FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-FC-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-FC FN2-FC FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-FC-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-FC FN2-FC FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-B3-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-B3 FN2-B3 FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-B3-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-B3 FN2-B3 FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-FIELDS-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-FIELDS FN2-FIELDS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-FIELDS-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-FIELDS FN2-FIELDS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-DIGESTS-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (UPDATE-FN2-CORE-DIGESTS FN2-DIGESTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-DIGESTS-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (UPDATE-FN2-CORE-DIGESTS FN2-DIGESTS FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-FORMAT-CORE-FN2-ENV-EK
  (IMPLIES
         (FN2-ENV-EK FN2-CORE FN2-REL-C0)
         (FN2-ENV-EK
              (MV-NTH '1
                      (FN2-COMMIT-FORMAT-CORE ID KIND ROLE OFF LEN FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-FORMAT-CORE-FN2-ENV-RK
  (IMPLIES
         (FN2-ENV-RK FN2-CORE FN2-REL-C0)
         (FN2-ENV-RK
              (MV-NTH '1
                      (FN2-COMMIT-FORMAT-CORE ID KIND ROLE OFF LEN FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-PACK-CORE-FN2-ENV-EK
  (IMPLIES
         (FN2-ENV-EK FN2-CORE FN2-REL-C0)
         (FN2-ENV-EK
              (MV-NTH '2
                      (FN2-COMMIT-PACK-CORE ID KIND ROLE INDEX OFF FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-PACK-CORE-FN2-ENV-RK
  (IMPLIES
         (FN2-ENV-RK FN2-CORE FN2-REL-C0)
         (FN2-ENV-RK
              (MV-NTH '2
                      (FN2-COMMIT-PACK-CORE ID KIND ROLE INDEX OFF FN2-CORE))
              FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-TXN-FRAME-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK
        (MV-NTH '4
                (FN2-COMMIT-TXN-FRAME BASE SLOT
                                      GEN OFF END OKIND OSLOT OGEN FN2-CORE))
        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-TXN-FRAME-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK
        (MV-NTH '4
                (FN2-COMMIT-TXN-FRAME BASE SLOT
                                      GEN OFF END OKIND OSLOT OGEN FN2-CORE))
        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-TXN-HEADER-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK
       (MV-NTH '2
               (FN2-COMMIT-TXN-HEADER RKIND EVENT BASE DST
                                      DG CURSOR SCRATCH SG ID OGEN FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-TXN-HEADER-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK
       (MV-NTH '2
               (FN2-COMMIT-TXN-HEADER RKIND EVENT BASE DST
                                      DG CURSOR SCRATCH SG ID OGEN FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-COPY-IN-FN2-ENV-EK
  (IMPLIES
     (FN2-ENV-EK FN2-CORE FN2-REL-C0)
     (FN2-ENV-EK
          (MV-NTH '1
                  (FN2-COMMIT-COPY-IN LEFT DST DG OFF FROM
                                      FG AT FKIND FID FGEN ID OGEN FN2-CORE))
          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-COPY-IN-FN2-ENV-RK
  (IMPLIES
     (FN2-ENV-RK FN2-CORE FN2-REL-C0)
     (FN2-ENV-RK
          (MV-NTH '1
                  (FN2-COMMIT-COPY-IN LEFT DST DG OFF FROM
                                      FG AT FKIND FID FGEN ID OGEN FN2-CORE))
          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SEAL-TXN-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK
        (MV-NTH '2
                (FN2-COMMIT-SEAL-TXN LEFT
                                     ID BASE WSLOT WGEN WOFF WEND OKIND OSLOT
                                     OGEN EVENT DST DG CURSOR FN2-CORE))
        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SEAL-TXN-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK
        (MV-NTH '2
                (FN2-COMMIT-SEAL-TXN LEFT
                                     ID BASE WSLOT WGEN WOFF WEND OKIND OSLOT
                                     OGEN EVENT DST DG CURSOR FN2-CORE))
        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SEAL-MEMBER-FN2-ENV-EK
  (IMPLIES
     (FN2-ENV-EK FN2-CORE FN2-REL-C0)
     (FN2-ENV-EK
          (MV-NTH '2
                  (FN2-COMMIT-SEAL-MEMBER ID INDEX CURSOR SLOT GEN FN2-CORE))
          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SEAL-MEMBER-FN2-ENV-RK
  (IMPLIES
     (FN2-ENV-RK FN2-CORE FN2-REL-C0)
     (FN2-ENV-RK
          (MV-NTH '2
                  (FN2-COMMIT-SEAL-MEMBER ID INDEX CURSOR SLOT GEN FN2-CORE))
          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SEAL-RECORDS-FN2-ENV-EK
  (IMPLIES
          (FN2-ENV-EK FN2-CORE FN2-REL-C0)
          (FN2-ENV-EK (MV-NTH '1
                              (FN2-COMMIT-SEAL-RECORDS ID SLOT GEN FN2-CORE))
                      FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SEAL-RECORDS-FN2-ENV-RK
  (IMPLIES
          (FN2-ENV-RK FN2-CORE FN2-REL-C0)
          (FN2-ENV-RK (MV-NTH '1
                              (FN2-COMMIT-SEAL-RECORDS ID SLOT GEN FN2-CORE))
                      FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-FC-CONTEXT-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
             (FN2-ENV-EK (UPDATE-FN2-CORE-FC-CONTEXT FN2-FC-CONTEXT FN2-CORE)
                         FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-FC-CONTEXT-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
             (FN2-ENV-RK (UPDATE-FN2-CORE-FC-CONTEXT FN2-FC-CONTEXT FN2-CORE)
                         FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-CONTEXT-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-CONTEXT ID ROLE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-CONTEXT-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-CONTEXT ID ROLE FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SEAL-FRAME-HEADER-FN2-ENV-EK
  (IMPLIES
       (FN2-ENV-EK FN2-CORE FN2-REL-C0)
       (FN2-ENV-EK
            (MV-NTH '1
                    (FN2-COMMIT-SEAL-FRAME-HEADER ID ROLE SLOT GEN FN2-CORE))
            FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SEAL-FRAME-HEADER-FN2-ENV-RK
  (IMPLIES
       (FN2-ENV-RK FN2-CORE FN2-REL-C0)
       (FN2-ENV-RK
            (MV-NTH '1
                    (FN2-COMMIT-SEAL-FRAME-HEADER ID ROLE SLOT GEN FN2-CORE))
            FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-PAGE-HASH-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (MV-NTH '1
                                   (FN2-COMMIT-PAGE-HASH ID STAGE FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-PAGE-HASH-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (MV-NTH '1
                                   (FN2-COMMIT-PAGE-HASH ID STAGE FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SEAL-CONTEXT-FN2-ENV-EK
  (IMPLIES
          (FN2-ENV-EK FN2-CORE FN2-REL-C0)
          (FN2-ENV-EK (MV-NTH '1
                              (FN2-COMMIT-SEAL-CONTEXT ID PREVIOUS FN2-CORE))
                      FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SEAL-CONTEXT-FN2-ENV-RK
  (IMPLIES
          (FN2-ENV-RK FN2-CORE FN2-REL-C0)
          (FN2-ENV-RK (MV-NTH '1
                              (FN2-COMMIT-SEAL-CONTEXT ID PREVIOUS FN2-CORE))
                      FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-ZERO-FN2-ENV-EK
  (IMPLIES
     (FN2-ENV-EK FN2-CORE FN2-REL-C0)
     (FN2-ENV-EK (MV-NTH '1
                         (FN2-COMMIT-ZERO LEFT AT SLOT GEN ID OGEN FN2-CORE))
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-ZERO-FN2-ENV-RK
  (IMPLIES
     (FN2-ENV-RK FN2-CORE FN2-REL-C0)
     (FN2-ENV-RK (MV-NTH '1
                         (FN2-COMMIT-ZERO LEFT AT SLOT GEN ID OGEN FN2-CORE))
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SEAL-STEP-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (MV-NTH '1
                                   (FN2-COMMIT-SEAL-STEP ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SEAL-STEP-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (MV-NTH '1
                                   (FN2-COMMIT-SEAL-STEP ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-ISSUED-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-ISSUED
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-STAGE
                                FN2-ARMS-W-CB-ISSUED FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-ISSUED-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+CB-STAGE+CB-ISSUED
                                ID FN2-ARMS-W-PHASE FN2-ARMS-W-CB-STAGE
                                FN2-ARMS-W-CB-ISSUED FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RUN-SEAL-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (MV-NTH '4
                                   (FN2-COMMIT-RUN-SEAL ID BUDGET FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-RUN-SEAL-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (MV-NTH '4
                                   (FN2-COMMIT-RUN-SEAL ID BUDGET FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+CB-OPEN-FN2-ENV-RK
  (IMPLIES
     (FN2-ENV-RK FN2-CORE FN2-REL-C0)
     (FN2-ENV-RK (FN2-COMMIT-WRITE+PHASE+CB-OPEN ID FN2-ARMS-W-PHASE
                                                 FN2-ARMS-W-CB-OPEN FN2-CORE)
                 FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RUN-COLLECT-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
             (FN2-ENV-RK (MV-NTH '4
                                 (FN2-COMMIT-RUN-COLLECT ID BUDGET FN2-CORE))
                         FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK
    (MV-NTH '4
            (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
    FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK
    (MV-NTH '4
            (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
    FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-FN2-ENV-FK
  (IMPLIES
   (FN2-ENV-FK FN2-CORE FN2-REL-C0)
   (FN2-ENV-FK
    (MV-NTH '4
            (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
    FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-FK) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-FN2-ENV-DK
  (IMPLIES
   (FN2-ENV-DK FN2-CORE FN2-REL-C0)
   (FN2-ENV-DK
    (MV-NTH '4
            (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                        STEPS DESCRIPTORS RUNNABLE FN2-CORE))
    FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DK) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-KEEPS-COMMIT-IO
  (EQUAL
   (NTH
      '30
      (MV-NTH
           '4
           (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                       STEPS DESCRIPTORS RUNNABLE FN2-CORE)))
   (NTH '30 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-io-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-IO-VIEW) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-KEEPS-COMMIT-ROOT
  (EQUAL
   (NTH
      '31
      (MV-NTH
           '4
           (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                       STEPS DESCRIPTORS RUNNABLE FN2-CORE)))
   (NTH '31 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-root-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-ROOT-TABLE-VIEW) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-KEEPS-COMMIT-TABLE
  (EQUAL
   (NTH
      '9
      (MV-NTH
           '4
           (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                       STEPS DESCRIPTORS RUNNABLE FN2-CORE)))
   (NTH '9 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-commit-table-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-COMMIT-TABLE-VIEW) clause world))))

(defthm FN2-MACHINE-CONTRACT-CHECK-KEEPS-DIRECTORY
  (EQUAL
   (NTH
      '3
      (MV-NTH
           '4
           (FN2-MACHINE-CONTRACT-CHECK OK BYTES
                                       STEPS DESCRIPTORS RUNNABLE FN2-CORE)))
   (NTH '3 FN2-CORE))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (union-theories '(fn2-env-directory-view) (theory 'fn2-column-projection-base)))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-DIRECTORY-VIEW) clause world))))

(defthm FN2-CORE-RESERVE-FN2-ENV-EK
  (IMPLIES
      (FN2-ENV-EK FN2-CORE FN2-REL-C0)
      (FN2-ENV-EK (MV-NTH '3
                          (FN2-CORE-RESERVE CLASS OKIND OSLOT OGEN FN2-CORE))
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-CORE-RESERVE-FN2-ENV-RK
  (IMPLIES
      (FN2-ENV-RK FN2-CORE FN2-REL-C0)
      (FN2-ENV-RK (MV-NTH '3
                          (FN2-CORE-RESERVE CLASS OKIND OSLOT OGEN FN2-CORE))
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-CORE-RESERVE-FN2-ENV-TK
  (IMPLIES
      (FN2-ENV-TK FN2-CORE FN2-REL-C0)
      (FN2-ENV-TK (MV-NTH '3
                          (FN2-CORE-RESERVE CLASS OKIND OSLOT OGEN FN2-CORE))
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-CORE-RESERVE-FN2-ENV-SK
  (IMPLIES
      (FN2-ENV-SK FN2-CORE FN2-REL-C0)
      (FN2-ENV-SK (MV-NTH '3
                          (FN2-CORE-RESERVE CLASS OKIND OSLOT OGEN FN2-CORE))
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-CORE-RESERVE-FN2-ENV-OK
  (IMPLIES
      (FN2-ENV-OK FN2-CORE FN2-REL-C0)
      (FN2-ENV-OK (MV-NTH '3
                          (FN2-CORE-RESERVE CLASS OKIND OSLOT OGEN FN2-CORE))
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-SAVE-POOL-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-SAVE-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-SAVE-POOL-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-SAVE-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-SAVE-POOL-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (FN2-COMMIT-SAVE-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-SAVE-POOL-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (FN2-COMMIT-SAVE-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-SAVE-POOL-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (FN2-COMMIT-SAVE-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-KEEP-POOL-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-KEEP-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-KEEP-POOL-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-KEEP-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-KEEP-POOL-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (FN2-COMMIT-KEEP-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-KEEP-POOL-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (FN2-COMMIT-KEEP-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-KEEP-POOL-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (FN2-COMMIT-KEEP-POOL ID ROLE SLOT GEN FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-UNWIND-POOL-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
              (FN2-ENV-EK (FN2-COMMIT-UNWIND-POOL ID ROLE OWNER-GEN FN2-CORE)
                          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-UNWIND-POOL-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
              (FN2-ENV-RK (FN2-COMMIT-UNWIND-POOL ID ROLE OWNER-GEN FN2-CORE)
                          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-UNWIND-POOL-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
              (FN2-ENV-TK (FN2-COMMIT-UNWIND-POOL ID ROLE OWNER-GEN FN2-CORE)
                          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-UNWIND-POOL-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
              (FN2-ENV-SK (FN2-COMMIT-UNWIND-POOL ID ROLE OWNER-GEN FN2-CORE)
                          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-UNWIND-POOL-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
              (FN2-ENV-OK (FN2-COMMIT-UNWIND-POOL ID ROLE OWNER-GEN FN2-CORE)
                          FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-RESERVE-POOLS-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK (MV-NTH '1
                       (FN2-COMMIT-RESERVE-POOLS LEFT ID OWNER-GEN FN2-CORE))
               FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RESERVE-EXTENT-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (MV-NTH '1
                                   (FN2-COMMIT-RESERVE-EXTENT ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RESERVE-EXTENT-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (MV-NTH '1
                                   (FN2-COMMIT-RESERVE-EXTENT ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-RESERVE-EXTENT-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (MV-NTH '1
                                   (FN2-COMMIT-RESERVE-EXTENT ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-RESERVE-EXTENT-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (MV-NTH '1
                                   (FN2-COMMIT-RESERVE-EXTENT ID FN2-CORE))
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOLS-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
            (FN2-ENV-RK (FN2-COMMIT-RELEASE-POOLS LEFT ID OWNER-GEN FN2-CORE)
                        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOLS-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
            (FN2-ENV-TK (FN2-COMMIT-RELEASE-POOLS LEFT ID OWNER-GEN FN2-CORE)
                        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOLS-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
            (FN2-ENV-SK (FN2-COMMIT-RELEASE-POOLS LEFT ID OWNER-GEN FN2-CORE)
                        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-RELEASE-POOLS-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
            (FN2-ENV-OK (FN2-COMMIT-RELEASE-POOLS LEFT ID OWNER-GEN FN2-CORE)
                        FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+GENERATION+PRINCIPAL-SLOT+DEADLINE+STOPPED+BATCH-NO+MEMBER-COUNT+FIRST-KEY+PARTNER+CB-MODE+CB-STAGE+CB-CURSOR+CB-ISSUED+CB-DONE+CB-BYTES+CB-FAILED+OUTCOME+CB-REASON+CB-FENCE-LIVE+CB-FENCE-OK+CB-DEPS-OK+CB-LOG-OK+CB-PUBLISHED+CB-ACKS+CB-SEAL-LEN+CB-WROTE+CB-OPEN+DEP-BYTES+REC-BYTES-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (FN2-COMMIT-WRITE+PHASE+GENERATION+PRINCIPAL-SLOT+DEADLINE+STOPPED+BATCH-NO+MEMBER-COUNT+FIRST-KEY+PARTNER+CB-MODE+CB-STAGE+CB-CURSOR+CB-ISSUED+CB-DONE+CB-BYTES+CB-FAILED+OUTCOME+CB-REASON+CB-FENCE-LIVE+CB-FENCE-OK+CB-DEPS-OK+CB-LOG-OK+CB-PUBLISHED+CB-ACKS+CB-SEAL-LEN+CB-WROTE+CB-OPEN+DEP-BYTES+REC-BYTES
                                ID
                                FN2-ARMS-W-PHASE FN2-ARMS-W-GENERATION
                                FN2-ARMS-W-PRINCIPAL-SLOT
                                FN2-ARMS-W-DEADLINE
                                FN2-ARMS-W-STOPPED FN2-ARMS-W-BATCH-NO
                                FN2-ARMS-W-MEMBER-COUNT
                                FN2-ARMS-W-FIRST-KEY
                                FN2-ARMS-W-PARTNER FN2-ARMS-W-CB-MODE
                                FN2-ARMS-W-CB-STAGE FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-ISSUED FN2-ARMS-W-CB-DONE
                                FN2-ARMS-W-CB-BYTES FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-OUTCOME FN2-ARMS-W-CB-REASON
                                FN2-ARMS-W-CB-FENCE-LIVE
                                FN2-ARMS-W-CB-FENCE-OK
                                FN2-ARMS-W-CB-DEPS-OK
                                FN2-ARMS-W-CB-LOG-OK
                                FN2-ARMS-W-CB-PUBLISHED
                                FN2-ARMS-W-CB-ACKS
                                FN2-ARMS-W-CB-SEAL-LEN
                                FN2-ARMS-W-CB-WROTE
                                FN2-ARMS-W-CB-OPEN FN2-ARMS-W-DEP-BYTES
                                FN2-ARMS-W-REC-BYTES FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-WRITE+PHASE+GENERATION+PRINCIPAL-SLOT+DEADLINE+STOPPED+BATCH-NO+MEMBER-COUNT+FIRST-KEY+PARTNER+CB-MODE+CB-STAGE+CB-CURSOR+CB-ISSUED+CB-DONE+CB-BYTES+CB-FAILED+OUTCOME+CB-REASON+CB-FENCE-LIVE+CB-FENCE-OK+CB-DEPS-OK+CB-LOG-OK+CB-PUBLISHED+CB-ACKS+CB-SEAL-LEN+CB-WROTE+CB-OPEN+DEP-BYTES+REC-BYTES-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (FN2-COMMIT-WRITE+PHASE+GENERATION+PRINCIPAL-SLOT+DEADLINE+STOPPED+BATCH-NO+MEMBER-COUNT+FIRST-KEY+PARTNER+CB-MODE+CB-STAGE+CB-CURSOR+CB-ISSUED+CB-DONE+CB-BYTES+CB-FAILED+OUTCOME+CB-REASON+CB-FENCE-LIVE+CB-FENCE-OK+CB-DEPS-OK+CB-LOG-OK+CB-PUBLISHED+CB-ACKS+CB-SEAL-LEN+CB-WROTE+CB-OPEN+DEP-BYTES+REC-BYTES
                                ID
                                FN2-ARMS-W-PHASE FN2-ARMS-W-GENERATION
                                FN2-ARMS-W-PRINCIPAL-SLOT
                                FN2-ARMS-W-DEADLINE
                                FN2-ARMS-W-STOPPED FN2-ARMS-W-BATCH-NO
                                FN2-ARMS-W-MEMBER-COUNT
                                FN2-ARMS-W-FIRST-KEY
                                FN2-ARMS-W-PARTNER FN2-ARMS-W-CB-MODE
                                FN2-ARMS-W-CB-STAGE FN2-ARMS-W-CB-CURSOR
                                FN2-ARMS-W-CB-ISSUED FN2-ARMS-W-CB-DONE
                                FN2-ARMS-W-CB-BYTES FN2-ARMS-W-CB-FAILED
                                FN2-ARMS-W-OUTCOME FN2-ARMS-W-CB-REASON
                                FN2-ARMS-W-CB-FENCE-LIVE
                                FN2-ARMS-W-CB-FENCE-OK
                                FN2-ARMS-W-CB-DEPS-OK
                                FN2-ARMS-W-CB-LOG-OK
                                FN2-ARMS-W-CB-PUBLISHED
                                FN2-ARMS-W-CB-ACKS
                                FN2-ARMS-W-CB-SEAL-LEN
                                FN2-ARMS-W-CB-WROTE
                                FN2-ARMS-W-CB-OPEN FN2-ARMS-W-DEP-BYTES
                                FN2-ARMS-W-REC-BYTES FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-PREPARE-ROOT-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-PREPARE-ROOT ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-PREPARE-ROOT-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-PREPARE-ROOT ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-PREPARE-ROOT-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (FN2-COMMIT-PREPARE-ROOT ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-PREPARE-ROOT-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (FN2-COMMIT-PREPARE-ROOT ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-PREPARE-ROOT-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (FN2-COMMIT-PREPARE-ROOT ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-READY-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
               (FN2-ENV-EK (FN2-COMMIT-READY ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-READY-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
               (FN2-ENV-RK (FN2-COMMIT-READY ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-READY-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
               (FN2-ENV-TK (FN2-COMMIT-READY ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-READY-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
               (FN2-ENV-SK (FN2-COMMIT-READY ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-READY-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
               (FN2-ENV-OK (FN2-COMMIT-READY ID FN2-CORE)
                           FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-MEMBERS-FN2-ENV-EK
  (IMPLIES
      (FN2-ENV-EK FN2-CORE FN2-REL-C0)
      (FN2-ENV-EK (UPDATE-FN2-CORE-COMMIT-MEMBERS FN2-COMMIT-MEMBER FN2-CORE)
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-MEMBERS-FN2-ENV-RK
  (IMPLIES
      (FN2-ENV-RK FN2-CORE FN2-REL-C0)
      (FN2-ENV-RK (UPDATE-FN2-CORE-COMMIT-MEMBERS FN2-COMMIT-MEMBER FN2-CORE)
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-MEMBERS-FN2-ENV-TK
  (IMPLIES
      (FN2-ENV-TK FN2-CORE FN2-REL-C0)
      (FN2-ENV-TK (UPDATE-FN2-CORE-COMMIT-MEMBERS FN2-COMMIT-MEMBER FN2-CORE)
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-MEMBERS-FN2-ENV-SK
  (IMPLIES
      (FN2-ENV-SK FN2-CORE FN2-REL-C0)
      (FN2-ENV-SK (UPDATE-FN2-CORE-COMMIT-MEMBERS FN2-COMMIT-MEMBER FN2-CORE)
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm UPDATE-FN2-CORE-COMMIT-MEMBERS-FN2-ENV-OK
  (IMPLIES
      (FN2-ENV-OK FN2-CORE FN2-REL-C0)
      (FN2-ENV-OK (UPDATE-FN2-CORE-COMMIT-MEMBERS FN2-COMMIT-MEMBER FN2-CORE)
                  FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-COMMIT-PUT-MEMBERS-FN2-ENV-EK
  (IMPLIES
   (FN2-ENV-EK FN2-CORE FN2-REL-C0)
   (FN2-ENV-EK
       (MV-NTH '1
               (FN2-COMMIT-PUT-MEMBERS LEFT M ROW
                                       KIND OKIND OSLOT OGEN EVENT FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-COMMIT-PUT-MEMBERS-FN2-ENV-RK
  (IMPLIES
   (FN2-ENV-RK FN2-CORE FN2-REL-C0)
   (FN2-ENV-RK
       (MV-NTH '1
               (FN2-COMMIT-PUT-MEMBERS LEFT M ROW
                                       KIND OKIND OSLOT OGEN EVENT FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-COMMIT-PUT-MEMBERS-FN2-ENV-TK
  (IMPLIES
   (FN2-ENV-TK FN2-CORE FN2-REL-C0)
   (FN2-ENV-TK
       (MV-NTH '1
               (FN2-COMMIT-PUT-MEMBERS LEFT M ROW
                                       KIND OKIND OSLOT OGEN EVENT FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-COMMIT-PUT-MEMBERS-FN2-ENV-SK
  (IMPLIES
   (FN2-ENV-SK FN2-CORE FN2-REL-C0)
   (FN2-ENV-SK
       (MV-NTH '1
               (FN2-COMMIT-PUT-MEMBERS LEFT M ROW
                                       KIND OKIND OSLOT OGEN EVENT FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-COMMIT-PUT-MEMBERS-FN2-ENV-OK
  (IMPLIES
   (FN2-ENV-OK FN2-CORE FN2-REL-C0)
   (FN2-ENV-OK
       (MV-NTH '1
               (FN2-COMMIT-PUT-MEMBERS LEFT M ROW
                                       KIND OKIND OSLOT OGEN EVENT FN2-CORE))
       FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

(defthm FN2-EXEC-WAKE-FN2-ENV-EK
  (IMPLIES (FN2-ENV-EK FN2-CORE FN2-REL-C0)
                                    (FN2-ENV-EK (FN2-EXEC-WAKE ID FN2-CORE)
                                                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-EK) clause world))))

(defthm FN2-EXEC-WAKE-FN2-ENV-RK
  (IMPLIES (FN2-ENV-RK FN2-CORE FN2-REL-C0)
                                    (FN2-ENV-RK (FN2-EXEC-WAKE ID FN2-CORE)
                                                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-RK) clause world))))

(defthm FN2-EXEC-WAKE-FN2-ENV-TK
  (IMPLIES (FN2-ENV-TK FN2-CORE FN2-REL-C0)
                                    (FN2-ENV-TK (FN2-EXEC-WAKE ID FN2-CORE)
                                                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-TK) clause world))))

(defthm FN2-EXEC-WAKE-FN2-ENV-SK
  (IMPLIES (FN2-ENV-SK FN2-CORE FN2-REL-C0)
                                    (FN2-ENV-SK (FN2-EXEC-WAKE ID FN2-CORE)
                                                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-SK) clause world))))

(defthm FN2-EXEC-WAKE-FN2-ENV-OK
  (IMPLIES (FN2-ENV-OK FN2-CORE FN2-REL-C0)
                                    (FN2-ENV-OK (FN2-EXEC-WAKE ID FN2-CORE)
                                                FN2-REL-C0))
  :rule-classes nil
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(FN2-ENV-OK) clause world))))

; An explicit counterexample accompanies the weak-claim rejection.
(assert-event
 (not (fn2-env-ek (update-nth 30 '((2)) nil) (update-nth 30 '((1)) nil))))
(must-fail
 (defthm fn2-column-whole-child-cannot-preserve-ek
  (fn2-env-ek (update-fn2-core-commit-io io fn2-core) fn2-core)
  :hints (("Goal" :do-not-induct t
           :in-theory (theory 'fn2-column-projection-base))
          (and stable-under-simplificationp (fn2-column-view-hint '(fn2-env-ek) clause world)))))
