// Synchronous FIFO, DEPTH = 2**AW entries of DW bits.
// Twin lab D5: the model checker proves it at one AW at a time; Lean proves
// the control logic for every AW (RtlProof/Examples/Fifo).

module fifo #(
  parameter int AW = 2,
  parameter int DW = 8
) (
  input  logic          clk,
  input  logic          rst,
  input  logic          push,
  input  logic          pop,
  input  logic [DW-1:0] din,
  output logic [DW-1:0] dout,
  output logic          full,
  output logic          empty,
  output logic [AW:0]   count
);
  localparam int DEPTH = 1 << AW;

  logic [DW-1:0] mem [DEPTH];
  logic [AW-1:0] rptr, wptr;

  assign full  = (count == DEPTH[AW:0]);
  assign empty = (count == '0);
  assign dout  = mem[rptr];

  logic do_push, do_pop;
  assign do_push = push && !full;      // a push into a full FIFO is dropped
  assign do_pop  = pop  && !empty;     // a pop from an empty FIFO is ignored

  always_ff @(posedge clk) begin
    if (rst) begin
      rptr  <= '0;
      wptr  <= '0;
      count <= '0;
    end else begin
      if (do_push) begin
        mem[wptr] <= din;
        wptr      <= wptr + 1'b1;
      end
      if (do_pop) rptr <= rptr + 1'b1;
      count <= count + {{AW{1'b0}}, do_push} - {{AW{1'b0}}, do_pop};
    end
  end

`ifdef FORMAL
  logic f_past_valid = 1'b0;
  always_ff @(posedge clk) f_past_valid <= 1'b1;
  always_comb if (!f_past_valid) assume (rst);

  // Jasper: assert property (@(posedge clk) disable iff (rst) count <= DEPTH);
  always_comb if (f_past_valid) p_count_le: assert (count <= DEPTH[AW:0]);
  // Pointer/count consistency (the "helper" a model checker usually needs too)
  always_comb if (f_past_valid) p_ptrs: assert (AW'(wptr - rptr) == count[AW-1:0]);
  // full and empty are never both set
  always_comb if (f_past_valid) p_not_full_and_empty: assert (!(full && empty));

  always_comb if (f_past_valid) c_full: cover (full);
`endif
endmodule
