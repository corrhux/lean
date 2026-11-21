"""sv2lean: translate synthesizable SystemVerilog (via Yosys) into a Lean 4 model.

Pipeline (docs/ARCHITECTURE.md §4.2):

    .sv ──Yosys (read -formal; prep; async2sync; dffunmap)──► JSON netlist
        ──ir.build──► typed IR (inputs, registers, combinational cells, properties)
        ──emit_lean.emit──► Lean: State, Input, Comb, comb, step, initOK,
                            assumptions, one predicate per assert/cover

Trust: the translator is not proven correct. `difftest` compares the Lean model
cycle-by-cycle against Yosys's own semantics (the `sat` pass, the same model
SymbiYosys checks) on random stimulus.
"""
