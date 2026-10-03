# How design questions get decided (ember, 2026-10-03)

The coordinator (Claude) and Astra (GPT-6-Astra via Codex) settle design questions between them.
ember is asked only when the two genuinely want her opinion.

1. A lane or the coordinator raises a question. The coordinator writes
   planning/design/<topic>-<date>.md: the rule today, why it came up, measurements,
   options, the coordinator's lean and what would change its mind.
2. The liaison runs a Codex CONSULTATION on that file (read-only worktree; implements nothing;
   it is asked to attack the lean, check the RFC/spec reading, and name what the file misses).
   Its answer is pasted verbatim with the liaison's source fact-check.
3. The coordinator replies in the file. If the two differ, one more round with the specific
   disagreement. Two rounds at most.
4. Outcome, recorded in a DECISION block with who decided:
   - AGREED: the coordinator decides, the lanes proceed, the spec/registry change lands with the code.
     ember sees it in the next status as one line with the file path. She can overturn it.
   - ESCALATE to ember only when: the two still disagree after two rounds; or both judge it a matter
     of product intent or taste that the sources cannot settle; or it is irreversible or outward-facing
     (deploy, publication, deletion, force-push, release definition).
   An escalation is short: the question, the two positions, what each would cost.
5. Sketches from the generator deputies and other design notes go through the same consultation.

## Astra is an empowered peer (ember, 2026-10-03)
Not only consulted. Astra (a) holds positions in design questions and may reject the framing;
(b) runs a standing review of COMPLETED work on dev ("what is wrong with the system as it stands"),
host concurrency first; (c) claims and implements workstreams of its own, audited by the liaison and
landed through the runner; (d) writes independent answers to the big questions, reconciled with the
Claude deputy's answer side by side.
