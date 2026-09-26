# fn lane friction, measured from the transcripts (2026-09-24 21:13 .. 2026-09-26 01:42 UTC)
Corpus: 186 sub-agent transcripts under three coordinator sessions (bbbe7a9b 09-24 night,
c42b4ed8 09-25 day/night, 997a44b0 tonight's wave 2); 25,590 tool calls (24,782 Bash),
276 agent-hours wall. Read from the raw JSONL (the agents' thinking is redacted, so each
agent's intent comes from its Bash `description` fields and its final message). Nothing ran
on the boxes; the repo was only read. Ids below are `cv show` prefixes.
## 1. zsh is the shell, and lanes write bash (largest single source of failed calls)
- `grep -r ... --include=*.lisp` unquoted: `(eval):1: no matches found: --include=*.lisp`,
  165 failures in 108 agents. All zsh NOMATCH failures: 303 in 141 of 186 agents (--include
  globs, `books/*.acl2`, `tools/*baseline*`, `docs/rfc*`).
- No word splitting of `$ROOTS`: a variable holding `--affected-by A --affected-by B` or a
  list of roots reaches farm.py as ONE argument. Measured: 13 failed submits in 10 lanes
  (e.g. spike-peering af35c1a3, control-c1 a624b2d6, fan-in a41ee0f8, night deputy a06ed223);
  each fix was described as "Resubmit with proper word splitting". Six lanes found `${=R}`
  independently. Also seen: `argument action: invalid choice: ' --affected-by books/...'`.
- `echo =====` between two cats fails (zsh `=cmd` expansion): `(eval):1: ===== not found`.
  The second file in that command is never printed. Hit by 14 lanes, 10 of them
  continuations reading BRIEF-COMMON then their LANEDUMP (harness-repair-2 a2c642a1,
  mission-signed a2c8f517, bp-lifecycle-2 a2a8c63f, control-c3e a0476d44).
- Cost: about 330 wasted calls. The glob failures inside `;` chains print nothing more, so a
  lane can take the empty result to mean the text is absent. I could not count how often
  that happened.
- Alleviation: add to BRIEF-COMMON "## Shell": "The Bash tool runs zsh. Quote every glob
  (`--include='*.lisp'`, or use `git grep`/`rg`); zsh does not split `$VAR` (use an array
  or `${=VAR}`); never start a word with `=` (`echo '====='`)." ember could instead set
  `setopt no_nomatch sh_word_split; unsetopt equals` for agent shells (ember's config).
## 2. farm.py hides the reason a cache preflight failed
- `farm.py` (tools/farm.py:367) builds the message from `answer.stdout[-800:]` only. It drops
  stderr and the exit code. The lane therefore sees "installing from the cache did not
  complete ... Cache preflight: <the tail of a book list>", while the real error
  (certify_books' `book names must be repository-relative ...`, or `install-partial needs
  --toolchain-identity`) went to stderr.
- Hit in 41 results across 20 transcripts (16 lanes, including tonight's operator-walk a95d62f5
  and the night deputy). The next 4-5 calls were almost always the same reverse-engineering:
  "See the full preflight message -> Find preflight message source -> Read farm preflight logic
  -> Run the cache preflight manually on hbox" (live-status ad3732c8, P3b aada9b51,
  control-c3b a6944dc1, bp-budgets a6cf0497, control-c1 a624b2d6). That is about 80 calls,
  and it cost run numbers too (gate roots -r3/-r4/-r5 created for runs that never started ACL2).
- Alleviation (tools/farm.py): include stderr and the return code in `detail`, and put the
  first error line first. Validate book names and `--affected-by` words locally before the
  rsync. certify_books' BOOK_NAME rule and a check that no argument contains a space would
  have refused all 13 word-split submits for free. Optionally run a local reader check,
  which would have caught 3 "unbalanced close parenthesis" submits.
## 3. A red farm run costs 3-6 calls just to find which books failed
- 91 of about 300 observed runs finished red (125 lanes submitted runs). After a red run the
  lane's next calls are nearly identical every time: "Show run 1 summary without uncached
  list / Find run log location / Inspect manifest / Locate failing book log / Read the
  failure" (operator-walk, mission-signed, source-corpus-2, width-producers-2, visibility-join,
  reclaim-host x6, peer-keys, M4 ...). 91 calls in 61 agents are explicitly this search. 132 farm
  calls pipe through `grep -v uncached`, because the "uncached: books/..." list (hundreds of
  lines) buries the verdict. farm/proof_repl `--help` was read 100 times.
- Alleviation: have `farm.py wait` end with a fixed-form verdict block: failing books, the
  first `ACL2 Error`/`FAILED` form per book, the harvested local log path, and books over
  10 s with their times. Print the uncached list only under `--verbose` (or as a count).
  This removes the step every red run repeats.
## 4. Test books cause most red runs
- Of 87 red runs with a "Books that failed:" line, 27 failed ONLY on tests/acl2 books and 34
  more had a test book among the failures (61/87). Only 53 of about 125 submitting agents
  ever started a REPL on a tests/acl2 book. bp-lifecycle a290ee0f spent all three runs red,
  each on a proof it then fixed in the REPL ("Try structured sortedp-of-merge proof"), and
  ended with "the head has no certificate".
- Alleviation: add a BRIEF-COMMON line under Farm: "Before each run, `proof_repl.py start
  --through` every changed book AND its test book to the end on persvati. Submit only
  when every form you changed says ok. The farm certifies; it is not the proof loop."
## 5. OpenSSL 3.5 on hbox is rediscovered lane by lane
- Native starts refuse with `OpenSSL 3.5 or newer is required for ML-DSA`, or the openssl
  binary fails with `version OPENSSL_... not found`. About 20 agents hit this first and then spent
  2-4 calls on "Find how the image finds OpenSSL 3.5 / Look for an OpenSSL 3.5 install on
  hbox / Rebuild with OpenSSL prefix" (M6 a11728b9, M4 routing a34f0f59, spike-peering,
  bounds-p5 ace64854, tonight reclaim-lifecycle a643270b and width-boundary ac00d58a).
  107 agents set `FN_OPENSSL_PREFIX`/`LD_LIBRARY_PATH` by hand on about 600 commands.
- The prefix is documented only in NIGHT.md:150 and tools/runbooks/hbox-image-build.sh.
  BRIEF-COMMON and tools/build_native_host.sh (93 hbox uses) do not mention it, and the
  refusal (host/native/signatures.lisp:117) does not name the variable.
- Alleviation: have build_native_host.sh default FN_OPENSSL_PREFIX to
  /tank/fn/toolchains/openssl-3.5.8 on hbox, name FN_OPENSSL_PREFIX in the refusal text,
  and add one BRIEF line. Better: one `tools/hbox_native.sh NAME MODULE [--image dev|prod]`
  that ships the tree, builds under systemd-run with MemoryMax, runs the module and prints
  log SHAs. Today 145 agents hand-roll rsync (1,035 ship-tree calls) and lane-local
  image.sh scripts (c3e-image.sh, $L/image.sh).
## 6. `make check` is red in every lane by design (the generated ledger)
- BRIEF-COMMON says both "do not edit planning/ledger.* or planning/current.md" and "`make
  check` green in your worktree before you report". Any lane that touches books or registries
  gets `ERROR: ledger: planning/ledger.json: stale`: 112 make-check runs in 70 agents (13 of
  them tonight). Lanes then regenerate and revert by hand. reader-daily a1d7c4d4 reports
  "`make check` is green, but only after regenerating planning/ledger.* ... I did not commit
  those". width-producers-2 and the deputy both ran `git checkout -- planning/ledger.*`.
- Alleviation: a `make check-lane` target, or `FN_LANE=1`, that regenerates the three
  generated files into a temp dir and checks against those. Otherwise say it in the brief:
  "stale ledger/current.md is expected; run `make check` after `tools/ledger.py --write` and
  `tools/current_view.py --write`, and do not commit them."
## 7. Registry JSON conflicts at every merge
- 65 conflicted merges (43 by the deputies, 18 by lanes merging dev). Conflicted files:
  proofs.json 12, tests/scenarios/catalog.json 11, requirements.json 8, proof-events.json 7.
  merge_lane.sh three-way-merges only proofs.json. merge_rows/merge_requirements/
  merge_events.py exist but are run by hand (42 uses, deputies only). Lanes merging dev
  resolve by hand (137 "resolve/conflict" calls in 32 agents).
- Alleviation: register the four merge scripts as a git merge driver (`.gitattributes`
  `planning/proofs.json merge=fn-registry` etc. plus `git config merge.fn-registry.driver`).
  Lanes and deputy then get the same automatic resolution, and merge_lane.sh shrinks.
## 8. Waiting: foreground loops, self-matching pgrep, blocked sleeps
- 1,073 wait calls (until/sleep loops) in 153 agents, 39.6 h (14% of agent wall time);
  9% of all calls are polls.
- 214 foreground commands hit the 600 s Bash limit and were moved to the background
  (87 agents: 104 until-loops, 67 long ssh runs).
- 85 `sleep N; cat` calls were blocked by the harness (79 agents). Each cost one call.
- 45 wait loops use `until ! pgrep -f "farm.py wait hbox run-..."`. The loop's own `zsh -c`
  argv contains that pattern, so it never exits; 14 of the 36 Bash ones ran to the 600 s
  limit (e.g. mission-signed a2c8f517). CLAUDE.md already warns about this trap for ssh.
- Alleviation: add to BRIEF-COMMON: "Wait by starting the command with
  run_in_background and taking its notification (farm.py wait, native runs, image builds);
  never a foreground until-loop, never `pgrep -f`." A `tools/await_remote.sh BOX FILE
  PATTERN` for hbox logs would replace the roughly 100 hand-written `until ssh hbox grep -q`
  loops.
## 9. Late notifications overwrite the lane's final message
- Background waits left running after the report fire later, and the lane's last text
  becomes a reply to them: "That notification is the old wait on farm run 1 finally ending"
  (consumer-e2 a9b42c2c), "That notification is the earlier log comparison" (harness-repair
  afa8ac9c), "Both watches ... have now expired" (width-producers-2 a8c253fd). 5 of 186.
  The coordinator relays the final message, so the LANEDUMP summary is lost from it.
- Alleviation: add to BRIEF-COMMON: "Before the final message, TaskStop every background
  task and Monitor you started; the final message is the LANEDUMP summary and nothing
  after it."
## 10. Three lanes independently hit "B refuses A's signed article" tonight
- source-corpus-2 a34db3ac ("B refuses every article A sends it, and it doesn't say why"),
  the mission harness a9b99656 and mission-four-node a14d9eb7 ("B refuses A's signed report").
  mission-signed is now a fourth lane on it. The refusal carries no reason, so each lane
  diagnosed it on its own.
- Alleviation: one owner lane for the refusal, whose first step is a reason on the refusal line
  (a PKT). The coordinator routes other lanes' symptoms to that owner rather than
  re-diagnosing.
## Smaller items
- Rule slips tonight: `pkill -f` in the "Route Python clients" agent aa932824 (twice, on the
  laptop); 2 `git add -A <files>` (named files, harmless). Across all sessions: `--closure`
  6 times, `--jobs >2` 17 times, all before wave 2 (c42b4ed8/bbbe7a9b).
- 16 lanes stalled together 09-25 about 11:05 -> 18:30 (the API limit). I could not attribute
  it further.
- No farm slot or queue contention appeared in any output. I could not measure farm queue
  time separately from lane wait loops.
## What worked (keep)
- Lane-unique `.commitmsg`: 236 `commit -F <shared scratchpad>` before wave 2, 0 tonight.
  No interleaved writes to one scratch path by two agents (95 scratch paths had been shared).
- Ids assigned in the brief: 5 renumbering commits on 09-25 day ("collisions happened five
  times today"); none tonight beyond the lanes' own ids.
- Cache reuse on the farm ("installed 414 of 510 books from 14 origins").
