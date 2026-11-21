#!/bin/bash
# Regenerate the Lean models of the Ibex blocks used by the capstone (Track 2).
# Needs sv2v (github.com/zachjs/sv2v/releases) and Yosys (native or `pip install yowasp-yosys`).
#   capstone/ibex/generate.sh            write RtlProof/Generated/Ibex*.lean
#   capstone/ibex/generate.sh --difftest also compare each model with Yosys on random inputs
set -euo pipefail
cd "$(dirname "$0")/../.."
I=third_party/ibex
COMMON=(--sv2v -D SYNTHESIS -I "$I/vendor/lowrisc_ip/ip/prim/rtl" -I "$I/rtl" "$I/rtl/ibex_pkg.sv")
EXTRA=()
[ "${1:-}" = "--difftest" ] && EXTRA=(--difftest 6 --cycles 60)

# ALU, RV32B = RV32BNone
sv2lean "${COMMON[@]}" "$I/rtl/ibex_alu.sv" --top ibex_alu \
  --namespace Gen.IbexAlu -o RtlProof/Generated/IbexAlu.lean "${EXTRA[@]}"

# Compressed decoder, RV32ZC = RV32Zca (standard C only), BaseIsa = BaseIsaRV32I
sv2lean "${COMMON[@]}" "$I/rtl/ibex_compressed_decoder.sv" --top ibex_compressed_decoder \
  -P RV32ZC=0 -P BaseIsa=0 --namespace Gen.IbexCDec -o RtlProof/Generated/IbexCDec.lean "${EXTRA[@]}"

# Decoder, plain RV32I: RV32M = RV32MNone, RV32B = RV32BNone, BaseIsa = BaseIsaRV32I
sv2lean "${COMMON[@]}" "$I/rtl/ibex_cheriot_pkg.sv" "$I/rtl/ibex_decoder.sv" --top ibex_decoder \
  -P RV32M=0 -P RV32B=0 -P BaseIsa=0 --namespace Gen.IbexDec -o RtlProof/Generated/IbexDec.lean "${EXTRA[@]}"

# Register file (flip-flops), plain RV32I: BaseIsa = RV32I, RV32E = 0, no dummy instructions
sv2lean "${COMMON[@]}" "$I/rtl/ibex_cheriot_pkg.sv" "$I/rtl/ibex_register_file_ff.sv" --top ibex_register_file_ff \
  -P BaseIsa=0 -P RV32E=0 -P DummyInstructions=0 --namespace Gen.IbexRF -o RtlProof/Generated/IbexRF.lean "${EXTRA[@]}"
