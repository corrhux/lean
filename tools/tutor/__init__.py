"""tutor: a Lean/formal-verification tutor that explains in Jasper terms (SPEC §6.6).

The model gets the learner's question plus context (open file, Lean errors and
goals, the last `ftwin` result) and can call local tools: compile Lean, read
course chapters and project files, summarise counterexample waveforms, run a
twin. Rule: any Lean code it shows must have passed `check_lean` first.
"""
