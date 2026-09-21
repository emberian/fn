# Initializer error-origin regression

Source `fc1af5621e01fe2f8e1c0d7c55f4fe0ff1b43d59`, 2026-09-21,
macOS with SBCL 2.6.8. Invocation:

```
sbcl --script tests/native_io_progress.lisp
```

The process exited successfully and printed `native-io-progress: ok`.
The actual raw publication helper was exercised with substituted syscall
observations: link EEXIST reports existing without a directory barrier;
successful link followed by a barrier EEXIST or EIO reports uncertain;
the named post-link fault cut also reports uncertain after one link and
before a barrier. The last case caught a misplaced exception boundary:
the injection had escaped as a generic fault even though publication had
already been attempted. The correction moves that cut inside the ambiguous
publication handler. The suite also retains the real bounded-directory test.

Source SHA-256:

- `host/native/io.lisp`: `c95c85f4c9f8dd74f5cd79b2e7ca90823842c778bf0469cf84ac5afc8b96cb2f`
- `tests/native_io_progress.lisp`: `6f864c14733b4daf623fb19d4862d70ffcffa425046914d700e8d7e6a9f915e2`
- Captured one-line output: `95dcc46a0febb0b4d54f809ff0d2d5a617f62cdefabcf266937b4f0bfd5d857c`

This is an actual-helper classification regression with controlled observations,
not a new saved-image run, a power-loss test, or complete physical/model
correspondence. The separate initializer certificates and earlier process-death
tests retain their original source scope.
