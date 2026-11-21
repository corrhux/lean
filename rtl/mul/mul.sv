// Shift-and-add array multiplier, W x W -> W bits (wrapping, like `a * b` in
// SystemVerilog at width W and BitVec multiplication in Lean).
//
//   acc[0]   = 0
//   acc[i+1] = acc[i] + (b[i] ? a << i : 0)
//   p        = acc[W]
//
// Twin lab D6: SAT effort on `p == a * b` grows steeply with W, while one Lean
// proof covers every W (RtlProof/Examples/Mul).

module mul #(
  parameter int W = 8
) (
  input  logic [W-1:0] a,
  input  logic [W-1:0] b,
  output logic [W-1:0] p
);

  // acc[i] lives in bits [i*W +: W]
  logic [(W+1)*W-1:0] acc;
  assign acc[0 +: W] = '0;

  for (genvar i = 0; i < W; i++) begin : g_pp
    assign acc[(i+1)*W +: W] = acc[i*W +: W] + (b[i] ? (a << i) : {W{1'b0}});
  end

  assign p = acc[W*W +: W];

`ifdef FORMAL
  // Jasper: assert property (p == a * b);   (a combinational equivalence check)
  always_comb p_mul: assert (p == a * b);
`endif

endmodule
