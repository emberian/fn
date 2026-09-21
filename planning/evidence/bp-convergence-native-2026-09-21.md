# W13 native BP sequence/lifecycle convergence transcript

The tested source is local commit
`10fdd89427e33afe5472ef01a5a0f087669dde71` on `w13/bp-convergence`, copied
to `/Users/ember/dev/fn/build/lanes/w13-bp-convergence` on persvati.  Nothing
was deployed.  The farm copy has no Git metadata, so source identity is
additionally pinned by the artifact-set closure digest and the hashes below.

Farm run `run-20260921T081652Z-262e` certified the declared DTN runtime-root
union and its focused BP tests from an initially empty dedicated cache.  Its
archived manifest is
`planning/evidence/manifests/certify-20260921T081657Z-1438651.json` (SHA-256
`ac8947b030ba7f09d7bd6bdf06baf790068f38d51f12414429283a95fac5306d`).
All 118 closure books/tests passed in 832.727 seconds with four effective
jobs, ACL2 Version 8.7 and SBCL 2.6.8.  The conservative forbidden-facility
scan reported no findings; it is not macro expansion and says nothing about
installed ACL2/system books.

The DTN artifact loader selected and successfully loaded one complete set:

```text
artifact-set  3987d05321d58de10d499aa4d99a58c55040d425b30377440ba9605b9961bfb7
origin        /Users/ember/dev/fn/build/lanes/w13-bp-convergence
books         111
source        8ca574f615b3c547d190ed269264b2d23ebef827d889bb92e97993f10bccc8d5
toolchain     107f3ebd96e589b51e92a0e5082c626732b9dea8711a709c8400a5a27821f4f5
rejected      0
```

The certified native build command on persvati was:

```sh
FN_ACL2=$HOME/fn-tools/acl2-8.7/saved_acl2 \
FN_NATIVE_BUILD=host/native/build-dtn.lisp \
FN_NATIVE_IMAGE=build/fn-host-dtn \
sh tools/build_native_host.sh
```

It exited zero and produced a 264M core.  The launcher SHA-256 is
`b51c5da9f55e4fab2da0f000c0e4cc9bcfe213ab7c459c2eac075fbb3b777cd3`,
the core SHA-256 is
`9e082c78c693075561dae56a4462991d39faea6b1b251af2600d7f0560cedb8a`,
and the build transcript SHA-256 is
`09ff40ff6f6f9d907718db42753af91a85302a75d042d81ff83f7a5394872f85`.
The remote and local hashes agree for the changed result-policy and lifecycle
sources: `host/bp-node-host.lisp` is
`6a9ee6ab6975a6b0a147652393031745a2ae81270da647ec2cbb6d25bdf98fe2`,
`host/native/bp.lisp` is
`30cae56312e0ceb0fdf801f753904f876440800330c981984b4f0da924b15480`,
`host/native/bp-service.lisp` is
`ce234b028d175287d1c0337a1c20221d4168c58171659f47b742504027d29b08`,
and `tests/test_bp_service_native.py` is
`a540d33c4883529c14d12166ade99be1ed692dd5aea565c743360e76bccdfae6`.

The following tests ran against that exact image and artifact set:

```sh
python3 tests/bp-dtn7/run_fn_bp_sequence_durability.py \
  --image build/fn-host-dtn \
  --work build/evidence-bp-sequence-union-linux \
  --source-revision 10fdd89 \
  --artifact-set 3987d05321d58de10d499aa4d99a58c55040d425b30377440ba9605b9961bfb7

python3 tests/bp-dtn7/run_fn_tcpcl_spool_recovery.py \
  --image build/fn-host-dtn \
  --work build/evidence-tcpcl-spool-union-linux \
  --source-revision 10fdd89 \
  --artifact-set 3987d05321d58de10d499aa4d99a58c55040d425b30377440ba9605b9961bfb7

python3 tools/tcpcl_lab.py --image build/fn-host-dtn \
  --work build/evidence-tcpcl-crash-union-linux --scenario crash

python3 -m unittest tests.test_bp_service_native -v
```

All passed.  Sequence recovery produced sequences 0 then 1, refused a real
held lock with exit 1, fenced root-publication and corrupt-frontier cases with
exit 3, and never authored at either fenced cut.  Spool recovery rejected a
reserved-name symlink with exit 4, fenced injected unlink and directory
barrier failures with exit 3, refused a competing live owner with exit 1, and
preserved the completed payload while removing its private stage.  Its report
SHA-256 is
`43bd4a9eaba9d48e028c42a2ce90003c4d2aced0373392a8de6292a57a5d3fa9`;
the sequence report is
`17f32840b5805fbc7a2facedb055e7849acd8645e408e59c288cf4c73df213cc`.

The deterministic crash scenario observed 118 receiver-side ACK events but
zero ACKs at the sender, confirmed the final ACK was withheld, then recovered
with the interrupted payload absent, no `.incoming-*` residue, and the prior
completed payload durable.  Its captured stdout SHA-256 is
`9709c9005780d6e5c2de906197014678d86bf4492bc6924a1226380f35c8e4fa`.

The four native BP lifecycle tests passed in 10.748 seconds; their transcript
SHA-256 is
`7bee4085577b193304dbaa3af3e8d84779fa55dd92bac5a7d46ff25a6f373f68`.
In particular, injected first and second lifecycle
directory-barrier failures are real `fnn-os-error` EIOs handled by the same
branch as failed `fsync`.  A visible byte-identical final record remains
uncertain, queue acceptance is withheld, no attempting/forwarding record is
added, and restart repeats the lifecycle-directory barrier before replay.  A
reachable duplex case also records one refused article and an uncertain
outbound TCPCL operation; the host-called ACL2 result policy returns uncertain
and the process exits 3.

This evidence does not prove filesystem or hardware power-loss semantics.
The sequence persistence theorem remains a model-specific trace result; an
actual host observation/return correspondence is separate W14 work.  Lifecycle
record naming and capacity are still host-owned, and the current service
recounts the bounded lifecycle namespace before each append; those ownership
and cost gaps remain open.  Native receive currently collapses an
`fnn-store-fault` to refusal, while the lifecycle sender collapses that same
base condition to uncertainty; core faults are therefore not yet preserved as
exit 4 on those paths.  An indeterminate receive-journal callback returns exit
3 but the outer accept loop can continue, so it is not yet a process-wide
mutation fence.  Finally, receive evidence names use a constant session tag
and a per-session transfer identifier with atomic replacement, so a later
session can overwrite a prior session's `.wire`/`.adu` evidence; an ACL2-owned
durable unique publication identity and no-replace conflict behavior remain to
be added.  No full DTN matrix was rerun, no application or archive receipt is
inferred from TCPCL transfer success, and no deployment was performed.
