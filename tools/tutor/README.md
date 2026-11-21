# tutor: an AI tutor that explains Lean in Jasper terms (milestone M6)

```sh
pip install -e ".[tutor]"
export ANTHROPIC_API_KEY=...            # or log in once with `ant auth login`

tutor ask "Why does bv_decide give me a counterexample in the step goal?" \
      --file RtlProof/Examples/Counter/Exercise.lean --level 2
tutor chat --design fifo --level 3      # interactive; /level N, /file PATH, /quit
ftwin tutor ask "..."                    # same thing, from ftwin
```

## What it does

Each question goes to Claude together with:

- the **hint level** (the ladder from SPEC FR-A2):

  | Level | Name | Shows code? |
  |---|---|---|
  | 1 | nudge | no |
  | 2 | concept | no |
  | 3 | tactic | at most one line |
  | 4 | step | the next step, compiled |
  | 5 | solution | a full proof, compiled |

- the **open file** (`--file`) and, for `.lean` files, **Lean's own messages for it**: errors with their goal states, and `sorry` warnings;
- the **twin lab** you're in (`--design`).

The model can call five local tools:

| Tool | Does |
|---|---|
| `check_lean` | compiles a snippet in this project (`import RtlProof` available) |
| `course_lookup` | finds course sections in `docs/*.md` by lesson number or keyword |
| `read_file` | reads project files (docs, RTL, Lean, tools only) |
| `cex_summary` | turns a counterexample `.vcd` into a per-step table |
| `run_ftwin` | runs both sides of a twin lab |

**Rule: it never shows Lean code it hasn't compiled with `check_lean`.** That is
enforced by the system prompt (ARCHITECTURE ADR-9).

## Configuration

| Variable | Default | |
|---|---|---|
| `TUTOR_MODEL` | `claude-opus-5-5` | any Claude model ID |
| `TUTOR_EFFORT` | `medium` | `low` … `max`; raise it for hard proofs |

On Claude Opus 5.5 the tutor also enables the API's server-side refusal
fallback (beta `server-side-fallback-2026-07-01`, `fallbacks: "default"`): if
a safety classifier declines a request, the API retries it on a fallback model
within the same call. The static system prompt is marked for prompt caching.
After each answer the CLI prints the tools used and the token counts (input,
cached, output).

## Tests

`tests/tutor` covers the tools and prompt assembly without calling the API.
The live API path has not been exercised in CI, which has no API key.
