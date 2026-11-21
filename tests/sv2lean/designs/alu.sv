// Exercises most cell types sv2lean supports: $add $sub $mul $neg $xor $or
// $not $shl $shr $sshr (signed) $lt (signed) $le $ne $eq $logic_* $reduce_*
// $pmux (case) $mux, slicing and concatenation.
module alu (
  input  logic       clk,
  input  logic [2:0] op,
  input  logic [7:0] a,
  input  logic [7:0] b,
  input  logic [2:0] sh,
  output logic [7:0] y,
  output logic       flag,
  output logic [7:0] prod,
  output logic [7:0] neg,
  output logic [3:0] acc
);
  logic        [7:0] r;
  logic signed [7:0] sa, sb;
  assign sa = a;
  assign sb = b;

  always_comb begin
    case (op)
      3'd0:    r = a + b;
      3'd1:    r = a - b;
      3'd2:    r = a ^ {b[3:0], b[7:4]};
      3'd3:    r = a << sh;
      3'd4:    r = a >> sh;
      3'd5:    r = sa >>> sh;
      3'd6:    r = {7'd0, sa < sb};
      default: r = {a[0], a[7:1]} | ~b;
    endcase
  end

  always_ff @(posedge clk) begin
    y    <= r;
    flag <= (^r) ^ (&a) ^ (|b) ^ (a <= b) ^ (a != b) ^ !a ^ (a && b) ^ (a == ~b);
    prod <= a * b;
    neg  <= -a;
    acc  <= (op == 3'd7) ? 4'd0 : acc + {1'b0, r[2:0]};
  end
endmodule
