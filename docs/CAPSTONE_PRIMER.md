# Capstone Primer — What exactly is being verified?

RISC-V, Sail, Ibex, RVFI, riscv-formal, and the proofs that connect them

Status: **Draft v1** · Reading for course Part E0 (before the Ibex capstone).
Companion to [CAPSTONE_IBEX.md](CAPSTONE_IBEX.md) and [COURSE.md](COURSE.md).

> Items marked **(verify)** are file names, signal names or details that must
> be checked against the pinned Ibex / sail-riscv / riscv-formal commits when
> the course chapter is written. Code snippets are simplified for teaching.

---

## 0. Why this primer exists

In Jasper terms, a processor proof has the usual three ingredients:

| Jasper ingredient | Processor-proof equivalent | Where it comes from |
|---|---|---|
| The **DUT** | Ibex RTL | lowRISC Ibex (SystemVerilog) |
| The **spec / reference model** | The RISC-V ISA, formally written in **Sail** | `sail-riscv` (RISC-V International's golden model) |
| The **checker / glue** | How DUT behaviour is compared with the spec: **RVFI** + riscv-formal, or the lowRISC Sail-equivalence harness | riscv-formal; Ibex's formal flow |

You cannot judge *what a proof means* without understanding all three — and,
crucially, the **glue**, because that is where the claim is actually stated.
This primer walks through each piece and ends with a coverage matrix showing
who proves what.

---

## 1. The verification stack (the picture to keep in mind)

```
   RISC-V ISA manuals (English prose: Unprivileged + Privileged specs)
                      │  formalised by hand (RISC-V International-adopted)
                      ▼
   ┌──────────────────────────────────┐
   │ Sail model  (sail-riscv)          │  ← "golden" executable, typed spec
   └──────┬──────────────┬─────────────┘
          │ sail → C++   │ sail → SystemVerilog        sail → Lean (optional)
          ▼              ▼                                  ▼
   emulator (run    reference model inside           Lean model of the ISA
   programs,        a formal harness                 (cross-check our
   compare traces)  (Jasper / Yosys+rIC3)            hand-written spec)
                         │
                         │  equivalence of observable behaviour
                         ▼
   ┌──────────────────────────────────┐   RVFI port   ┌────────────────────┐
   │ Ibex RTL (DUT)                    │──────────────►│ riscv-formal checks │
   └──────────────────────────────────┘                └────────────────────┘
          │ sub-blocks via sv2lean
          ▼
   Lean proofs of ALU / decoders / regfile / multdiv  vs.  our Lean RV32I spec
```

Three different correctness claims live in this picture — Section 8 compares them.

---

## 2. RISC-V essentials for a verifier

Only what you need to read Sail and Ibex.

### 2.1 Architectural state (what the spec talks about)
| State | RV32 | Notes |
|---|---|---|
| `pc` | 32 bits | address of current instruction |
| `x0..x31` | 32 × 32 bits | `x0` reads as 0, writes ignored |
| CSRs | 12-bit address space | `mstatus`, `mtvec`, `mepc`, `mcause`, `mtval`, `mie/mip`, counters… |
| Privilege mode | M / U (Ibex) / S (not in Ibex) | Ibex implements M and U |
| Memory | byte-addressed | **outside the core** — this matters (Section 7) |

### 2.2 Instruction formats (32-bit)
```
R: funct7 | rs2 | rs1 | funct3 | rd      | opcode    (ADD, SUB, SLL, …)
I: imm[11:0]    | rs1 | funct3 | rd      | opcode    (ADDI, loads, JALR)
S: imm[11:5]|rs2| rs1 | funct3 | imm[4:0]| opcode    (stores)
B: imm[12|10:5]|rs2|rs1|funct3|imm[4:1|11]|opcode   (branches — scrambled immediate)
U: imm[31:12]                  | rd      | opcode    (LUI, AUIPC)
J: imm[20|10:1|11|19:12]       | rd      | opcode    (JAL — scrambled immediate)
```
Immediates are always sign-extended. The scrambled B/J immediates are a classic
source of decoder bugs — and a nice `bv_decide` exercise.

### 2.3 Extensions relevant to Ibex
- **I** base integer · **M** multiply/divide · **C** compressed 16-bit
  instructions (each expands to exactly one 32-bit instruction) · **Zicsr**,
  **Zifencei** · optional **B** (bit-manipulation subsets).
- Bits `[1:0] == 2'b11` ⇒ 32-bit instruction; otherwise 16-bit (C).

### 2.4 Traps
Exceptions (illegal instruction, misaligned/faulting access, ECALL, EBREAK) and
interrupts redirect `pc` to `mtvec`, save `mepc`/`mcause`/`mtval`, change
privilege. **Most of the complexity of a real core proof lives here**, not in
ADD.

---

## 3. Sail — the ISA specification language

### 3.1 What Sail is
Sail is a domain-specific language for **instruction-set semantics**, developed
at Cambridge (REMS project) and used for RISC-V, Arm-A (translated from Arm's
ASL), CHERI, and others. It looks like a small imperative language but has:

- **Dependent bit-vector types**: `bits('n)` with integer constraints checked
  by an SMT solver at type-check time (no width-mismatch bugs in the spec).
- **Scattered definitions**: the instruction AST, decoder and `execute`
  function are spread across files, one clause per instruction family.
- **Bidirectional mappings** (`mapping`) so one definition gives both encode
  and decode (and assembly printing).
- **Multiple backends** from one source: C/C++ emulator, theorem provers
  (Isabelle, HOL4, Coq/Rocq historically via Lem; a newer **Lean** backend),
  SMT (used by tools like Isla), and **SystemVerilog** (built for the
  CHERIoT-Ibex Jasper proof).

The `sail-riscv` model is the **RISC-V International golden model**:
compliance tests are generated against it and disputes about the prose spec are
settled with it.

### 3.2 Reading Sail: one instruction end to end (simplified)

```sail
/* 1. AST constructor for the I-type ALU family */
union clause ast = ITYPE : (bits(12), regidx, regidx, iop)

/* 2. Encoding <-> decoding in one mapping */
mapping clause encdec = ITYPE(imm, rs1, rd, op)
  <-> imm @ rs1 @ encdec_iop(op) @ rd @ 0b0010011

/* 3. Semantics */
function clause execute (ITYPE(imm, rs1, rd, op)) = {
  let rs1_val = X(rs1);
  let immext : xlenbits = sign_extend(imm);
  let result : xlenbits = match op {
    RISCV_ADDI  => rs1_val + immext,
    RISCV_SLTI  => zero_extend(bool_to_bits(rs1_val <_s immext)),
    RISCV_SLTIU => zero_extend(bool_to_bits(rs1_val <_u immext)),
    RISCV_ANDI  => rs1_val & immext,
    RISCV_ORI   => rs1_val | immext,
    RISCV_XORI  => rs1_val ^ immext
  };
  X(rd) = result;
  RETIRE_SUCCESS
}
```

The same instruction in the course's Lean spec (`RtlProof/RV32I/Spec`):

```lean
| .itype imm rs1 rd op =>
    let v      := s.x rs1
    let immext := imm.signExtend 32
    let r : BitVec 32 := match op with
      | .addi  => v + immext
      | .slti  => if v.slt immext then 1 else 0
      | .sltiu => if v.ult immext then 1 else 0
      | .andi  => v &&& immext
      | .ori   => v ||| immext
      | .xori  => v ^^^ immext
    (s.setX rd r).advancePc
```

They are deliberately close. The Lean version is a *subset* (no traps, no
CSRs, RV32 only) written for readability; Sail is the full authority.

### 3.3 How the sail-riscv model is organised (verify file names)
| Area | Typical files | What it defines |
|---|---|---|
| Types & registers | `riscv_types.sail`, `riscv_regs.sail` | `regidx`, `X(..)` read/write (with x0 rule), `PC`, `nextPC` |
| Instructions | `riscv_insts_base.sail`, `riscv_insts_mext.sail`, `riscv_insts_cext.sail`, `riscv_insts_zicsr.sail` | AST clauses, `encdec`, `execute` |
| System | `riscv_sys_control.sail`, `riscv_sys_regs.sail` | traps, interrupts, CSRs, privilege |
| Memory | `riscv_mem.sail`, PMP files | memory accesses, alignment, PMP checks |
| Top-level loop | `riscv_step.sail` | **fetch → decode → execute → update PC**, interrupt check |
| Configuration | platform/config files | which extensions, misaligned-access policy, etc. |

Key reading skill: **follow `step`** — it is the "one cycle of the abstract
machine" and is exactly the function a processor proof compares one retired
instruction against.

### 3.4 Implementation-defined choices
The RISC-V spec leaves some behaviour to the implementation (e.g. misaligned
access: trap or handle in hardware; which `mtval` values are written; WARL CSR
fields). The Sail model is **configured** to match Ibex's choices for the
proof. When you read the Ibex proof, find that configuration — it is part of
the claim.

---

## 4. Ibex — a guided tour of the DUT

### 4.1 Top-level picture (default: 2 stages, no writeback stage)

```
             instr bus (req/gnt/rvalid/err)                data bus
                  │                                           ▲
 ┌────────────────▼───────────────┐   ┌───────────────────────┴──────────────┐
 │ IF stage  (ibex_if_stage)       │   │ ID/EX stage  (ibex_id_stage + ibex_ex_block)
 │  ibex_prefetch_buffer           │   │  ibex_decoder      ibex_controller (FSM:
 │   └ ibex_fetch_fifo             │──►│                     stalls, traps, debug)
 │  ibex_compressed_decoder (C→32) │   │  ibex_alu   ibex_multdiv_{fast,slow}
 │  [ibex_icache — optional]       │   │  ibex_load_store_unit (splits misaligned)
 └─────────────────────────────────┘   │  ibex_cs_registers (CSRs)  ibex_pmp (opt)
                                       └───────────┬───────────────────────────┘
                                                   │ write-back (or ibex_wb_stage
                                                   ▼  when WritebackStage=1)
                                     ibex_register_file_{ff,latch,fpga}
 ibex_top wraps ibex_core + register file + optional ICache RAMs + lockstep (SecureIbex)
```

### 4.2 Things that make Ibex harder than a textbook pipeline
- **Compressed instructions** are expanded in IF; the PC can advance by 2 or 4.
- **Prefetch buffer** fetches ahead; branches/jumps/traps must flush it.
- **Loads/stores are multi-cycle**; misaligned accesses become two bus
  transactions; bus errors become precise exceptions.
- **Multi-cycle mult/div** (slow variant iterates for ~32+ cycles).
- **Controller FSM** handles interrupts, debug mode entry/exit, WFI, flushes.
- **Security features** (SecureIbex: dummy instructions, data-independent
  timing, lockstep) — disabled for the course.

### 4.3 Where architectural state lives in Ibex (the abstraction map)
This table is the heart of any refinement proof — it is the **abstraction
function** from microarchitectural state to the spec's state. (verify signal names)

| Spec state (Sail / Lean) | Ibex location | Subtlety |
|---|---|---|
| `PC` | PC of the instruction in ID/EX (e.g. `pc_id`) | IF holds speculative PCs; only ID/EX's is architectural |
| `x1..x31` | register file array (e.g. `rf_reg` in `ibex_register_file_ff`) | pending writes from a load in flight; with WB stage, forwarding |
| `x0` | hard-wired / not stored | write-enable masked |
| CSRs | `ibex_cs_registers` (e.g. `mstatus`, `mepc`, `mcause`, `mtvec`) | WARL legalisation; some fields read-only |
| Privilege | e.g. `priv_mode_id` | changes on trap/MRET |
| Memory | **not in the DUT** | observed only as bus transactions |

### 4.4 Configurations
Generated from `ibex_configs.yaml` (`small`, `opentitan`, `maxperf`, …). The
course's minimal "capstone" config is in CAPSTONE_IBEX.md §3.

### 4.5 Seeing Ibex run (lab hooks)
- `examples/simple_system`: Ibex + RAM + UART-ish peripherals, simulated with
  **Verilator**; runs C programs compiled with a RISC-V GCC toolchain.
- `ibex_tracer` writes an **instruction trace** (`trace_core_*.log`) — derived
  from RVFI — one line per retired instruction.
- Compare that trace with the **Sail emulator's** trace for the same ELF: this
  is co-simulation, the simulation-world ancestor of the formal proof.

---

## 5. RVFI — the RISC-V Formal Interface

RVFI is a **trace port**: one record per *retired* instruction, emitted by the
core (in Ibex: under a `RVFI` define). It turns "the core's behaviour" into an
explicit stream that a checker can compare against the spec. Main fields:

| Field | Meaning |
|---|---|
| `rvfi_valid` | an instruction retires this cycle |
| `rvfi_order` | monotonically increasing instruction index |
| `rvfi_insn` | the instruction word (expanded or raw — check Ibex's convention, verify) |
| `rvfi_trap`, `rvfi_intr`, `rvfi_halt` | trap taken / first instruction of handler / halted |
| `rvfi_mode`, `rvfi_ixl` | privilege mode, XLEN |
| `rvfi_rs1_addr/rdata`, `rvfi_rs2_addr/rdata` | source registers and the values *the core actually used* |
| `rvfi_rd_addr/wdata` | destination register and value written |
| `rvfi_pc_rdata/wdata` | PC of this instruction / PC of the next one |
| `rvfi_mem_addr/rmask/wmask/rdata/wdata` | memory access made by this instruction |
| `rvfi_csr_*` (extension) | CSR reads/writes |

**Jasper analogy:** RVFI is the "transaction-level monitor" you'd write for an
end-to-end checker, except it is standardised and lives inside the DUT.

**Caveat to internalise:** RVFI is produced *by the DUT*. A bug in the RVFI
logic can hide a real bug — part of the trust base for RVFI-based checks.

---

## 6. riscv-formal — what its checks actually prove

riscv-formal (YosysHQ) is a library of SBY-driven checks over RVFI. Its key
idea is **decomposition**: no single check proves "the core is correct";
together they cover it.

| Check | Claim (at the checked retirement) |
|---|---|
| `insn_<name>` | *Given the operands the core reported* (`rs1_rdata`, `rs2_rdata`, `pc_rdata`, `mem_rdata`), the results (`rd_wdata`, `pc_wdata`, mem address/data/mask) match the ISA spec for that instruction |
| `reg` | The value reported as read from register *r* equals the last value reported written to *r* (by `rvfi_order`) |
| `pc_fwd` / `pc_bwd` | `pc_rdata` of instruction n+1 equals `pc_wdata` of instruction n |
| `causal` | Results are not consumed before they are produced (order consistency) |
| `unique` | No two retirements share the same `rvfi_order` |
| `liveness` | An instruction retires within a bound (no deadlock), under fairness of the memory |
| `ill` | Illegal encodings trap |
| `csrw` / CSR checks | CSR read/write behaviour |
| `cover` | Reachability sanity — the core can actually retire N instructions |

How it composes: `insn_*` checks semantics *relative to reported inputs*; `reg`
+ `pc_*` + `causal` check that the reported inputs are the *right* inputs. If
both hold for every instruction, the retirement stream matches the ISA.

Limits — important when comparing with Lean:
- **Bounded**: each check is BMC to a fixed depth (typically tens of cycles)
  from reset or a constrained state; deep bugs can escape.
- The spec models are riscv-formal's **own Verilog ISA models**, not Sail.
- Traps/CSRs/interrupts coverage is partial and core-dependent.
- Ibex's riscv-formal flow has historically run with **M disabled**.

---

## 7. The lowRISC Ibex ⇔ Sail proof — anatomy and reading guide

### 7.1 The claim
Published summary: Ibex and the Sail spec **perform the same memory operations,
in the same order, for equivalent inputs** — "observational correctness."

Why phrase correctness this way? Because (Section 4.3) **memory is outside the
core**: the only things the rest of the SoC can ever observe are bus
transactions (instruction fetches and data reads/writes). Two systems that
always issue the same memory operations in the same order, given the same
responses, are indistinguishable to the outside world. It also sidesteps
cycle-timing differences: Ibex and Sail have no common notion of "cycle", but
they do share the *order* of memory operations.

### 7.2 The machinery
- **Sail → SystemVerilog**: the Sail model is compiled into a large
  *combinational* SV module representing one spec step (an instruction, a
  fetch error, or an interrupt).
- **Harness**: when Ibex reaches a step boundary, the spec module is fed the
  architectural state (reconstructed via the abstraction map, Section 4.3) and
  the event; its outputs (next state, memory operations) are compared with
  what Ibex does.
- **Tools**: commercially, Jasper (CHERIoT-Ibex); openly, yosys-slang (with
  lowRISC's SVA-subset extension) → Yosys → AIGER → **rIC3**, orchestrated by a
  "proof conductor" that runs many properties concurrently. Runs in Ibex CI,
  converging in < ~45 min on a capable machine.
- **Lemma structure**: properties are ordered so that **earlier end-to-end
  results are assumed as lemmas for later ones**; consequently most properties
  close with **1- or 2-induction**. This is a theorem-proving discipline
  imposed on a model checker — see course chapter D10.

### 7.3 Reading guide — questions to answer when you open the flow
Use these while reading the Ibex formal directory and the DVClub slides:
1. What exact event marks a "step boundary" in Ibex? (retire? RVFI valid?)
2. How is the abstraction map from Ibex state to Sail state written?
3. Which Sail configuration options were chosen to match Ibex's
   implementation-defined behaviour?
4. Which features are excluded or constrained (debug? PMP? specific CSRs?)?
5. What invariants relate the prefetch buffer / LSU state to the
   architectural state? Which ones needed to be stated by hand?
6. What is the lemma dependency order, and which properties need k > 1?
7. What is in the trusted base: yosys-slang, Yosys, rIC3, the Sail→SV
   compiler, the Sail model, the harness itself?

### 7.4 Jasper mapping
| lowRISC open flow | Jasper equivalent |
|---|---|
| Sail→SV reference model | C2RTL-style reference model / scoreboard in SV |
| Lemma ordering, earlier results assumed | Helper assertions with `assume`-after-proof (proof structure / assume-guarantee) |
| Proof conductor running rIC3 jobs | Proof grid / session with engine portfolio |
| 1-/2-induction closing | Engine N/Hp-style induction succeeding after helpers are proven |

---

## 8. Who proves what — the coverage matrix

| Claim | riscv-formal (Track 1a) | Ibex⇔Sail proof (Track 1b) | Lean blocks (Track 2) | Lean slice (Track 3) |
|---|---|---|---|---|
| Spec used | riscv-formal Verilog ISA models | **Sail** (golden) | Our Lean RV32I(+C) spec | Our Lean spec |
| Scope | Whole core, via RVFI | Whole core | Individual modules | Constrained ALU-instruction pipeline |
| Bounded? | **Yes** (BMC depth) | **No** (inductive) | No | No |
| Parametric (∀ width/depth)? | No | No | Where modelled parametrically | No |
| Traps / CSRs / interrupts | Partial | Yes (within config) | No | No (assumed away) |
| Trust base | Yosys, SBY, solver, RVFI logic, riscv-formal models | yosys-slang, Yosys, rIC3, Sail→SV, Sail model, harness | Lean kernel, `bv_decide` LRAT checker, **sv2lean + difftest**, our spec | same as Track 2 |
| Main lesson | decomposition into small bounded checks | lemma structure makes MC scale | SAT-in-prover for blocks; induction for iterative units | refinement on a real pipeline |

Optional cross-check: Sail→Lean output vs. our Lean spec ties the Lean tracks
to the same golden spec that Track 1b uses.

---

## 9. Glossary

| Term | Meaning |
|---|---|
| Architectural state | State defined by the ISA (pc, GPRs, CSRs, privilege, memory) |
| Microarchitectural state | Implementation state (pipeline registers, buffers, FSMs) |
| Abstraction function | Maps microarchitectural → architectural state |
| Retire | Point at which an instruction's effects become architectural |
| Refinement | Every implementation behaviour is a spec behaviour (via abstraction) |
| Observational correctness | Equivalence of externally visible behaviour (here: memory operation sequences) |
| RVFI | RISC-V Formal Interface — per-retirement trace port |
| Sail | ISA specification language; `sail-riscv` is the golden RISC-V model |
| WARL | "Write Any, Read Legal" CSR field behaviour |
| Co-simulation | Run DUT and spec emulator on the same program; compare traces |
| Flushing (Burch–Dill) | Abstraction that drains the pipeline to read off architectural state |

---

## 10. Sources
- lowRISC, *Open Source Correctness Proof for Ibex* — https://lowrisc.org/news/open-source-correctness-proof-for-ibex/
- *Comprehensive Formal Verification of Observational Correctness for the CHERIoT-Ibex Processor* — https://arxiv.org/abs/2502.04738
- Ploix, *Crossing the Model Checking / Theorem Proving Gap for Ibex Correctness*, DVClub Cambridge 2025 — https://alpinumconsulting.com/wp-content/uploads/Louis-Emile-Ploix-Crossing-the-Model-CheckingTheorem-Proving-Gap-for-Ibex-Correctness.pdf
- Ibex documentation — https://ibex-core.readthedocs.io/
- sail-riscv — https://github.com/riscv/sail-riscv
- Armstrong et al., *ISA Semantics for ARMv8-A, RISC-V, and CHERI-MIPS*, POPL 2019 (Sail).
- riscv-formal and RVFI documentation — https://github.com/YosysHQ/riscv-formal
- RISC-V Unprivileged and Privileged ISA specifications — https://riscv.org/specifications/
