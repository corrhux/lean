// BCD counter: counts 0..9 while `en` is high, then wraps to 0.
// The same design is modelled in Lean (docs/LEAN_FLUENCY.md, L14) and
// unrolled to CNF in satlab (`satlab gen counter-bmc`).
//
// WRAP is a parameter so the off-by-one bug (WRAP = 10) can be injected
// from the .sby file to produce a counterexample.

module counter #(
  parameter logic [3:0] WRAP = 4'd9
) (
  input  logic       clk,
  input  logic       rst,
  input  logic       en,
  output logic [3:0] cnt
);

  always_ff @(posedge clk) begin
    if (rst)     cnt <= 4'd0;
    else if (en) cnt <= (cnt == WRAP) ? 4'd0 : cnt + 4'd1;
  end

`ifdef FORMAL
  // Start in reset (Jasper: `reset rst` / `assume -reset`).
  logic f_past_valid = 1'b0;
  always_ff @(posedge clk) f_past_valid <= 1'b1;
  always_comb if (!f_past_valid) assume (rst);

  // p_le_9 — Jasper: assert property (@(posedge clk) disable iff (rst) cnt <= 9);
  always_comb if (f_past_valid) p_le_9: assert (cnt <= 4'd9);

  // p_hold — Jasper: assert property (@(posedge clk) disable iff (rst) !en |=> $stable(cnt));
  logic       f_en_q;
  logic       f_rst_q;
  logic [3:0] f_cnt_q;
  always_ff @(posedge clk) begin
    f_en_q  <= en;
    f_rst_q <= rst;
    f_cnt_q <= cnt;
  end
  always_comb if (f_past_valid && !f_rst_q && !f_en_q) p_hold: assert (cnt == f_cnt_q);

  // c_reach_9 — Jasper: cover property (cnt == 9);
  always_comb if (f_past_valid) c_reach_9: cover (cnt == 4'd9);
`endif

endmodule
