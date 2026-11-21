// Round-robin arbiter for N = 2**K requesters (twin lab D8).
//
// `ptr` is the requester with highest priority this cycle. The grant goes to
// the first requester at or after `ptr` (cyclically); next cycle the priority
// moves to the one after the granted requester.
//
// Implementation (no dynamic indexing):
//   rot     = requests rotated right by ptr       (rot[k] = req[(ptr+k) mod N])
//   rot_gnt = lowest set bit of rot                (rot & -rot)
//   gnt     = rot_gnt rotated back left by ptr
//   off     = index of the bit set in rot_gnt
//   ptr    <= ptr + off + 1

module arbiter #(
  parameter int K = 2,
  localparam int N = 1 << K
) (
  input  logic         clk,
  input  logic         rst,
  input  logic [N-1:0] req,
  output logic [N-1:0] gnt
);
  logic [K-1:0]   ptr;
  logic [2*N-1:0] dreq, dgnt;
  logic [N-1:0]   rot, rot_gnt;
  logic [K-1:0]   off;

  assign dreq    = {req, req} >> ptr;
  assign rot     = dreq[N-1:0];
  assign rot_gnt = rot & (~rot + 1'b1);
  assign dgnt    = {rot_gnt, rot_gnt} << ptr;
  assign gnt     = dgnt[2*N-1:N];

  always_comb begin
    off = '0;
    for (int k = 0; k < N; k++)
      if (rot_gnt[k]) off = k[K-1:0];
  end

  always_ff @(posedge clk) begin
    if (rst)          ptr <= '0;
    else if (|req)    ptr <= ptr + off + 1'b1;
  end

`ifdef FORMAL
  logic f_past_valid = 1'b0;
  always_ff @(posedge clk) f_past_valid <= 1'b1;
  always_comb if (!f_past_valid) assume (rst);

  // Safety (Jasper: assert property ($onehot0(gnt)); etc.)
  always_comb p_onehot: assert ((gnt & (gnt - 1'b1)) == '0);   // at most one grant
  always_comb p_valid:  assert ((gnt & ~req) == '0);           // only to requesters
  always_comb p_work:   assert (req == '0 || gnt != '0);       // never idle when requested

  // Fairness, for one arbitrary requester j (Jasper: a symbolic index via a
  // free constant, plus a watchdog counter). j must hold its request until granted.
  (* anyconst *) logic [K-1:0] f_j;
  logic f_req_j, f_gnt_j;
  assign f_req_j = |((req >> f_j) & 1);
  assign f_gnt_j = |((gnt >> f_j) & 1);

  logic f_waiting;                         // j requested last cycle and was not granted
  logic [K:0] f_wait;                      // consecutive cycles j has waited
  always_ff @(posedge clk) begin
    f_waiting <= f_past_valid && !rst && f_req_j && !f_gnt_j;
    if (rst || !f_req_j || f_gnt_j) f_wait <= '0;
    else                           f_wait <= f_wait + 1'b1;
  end
  always_comb if (f_past_valid && f_waiting) assume (f_req_j);   // request held until granted

  // j is granted within N cycles: it never waits N cycles in a row
  always_comb if (f_past_valid) p_fair: assert (f_wait < N);

  // Helper assertion (needed by k-induction at small k): j has waited at most
  // as many cycles as its distance from ptr has shrunk.
  logic [K-1:0] f_dist;
  assign f_dist = f_j - ptr;
  always_comb if (f_past_valid && f_wait != '0) p_fair_helper: assert (f_wait + f_dist < N);

  always_comb if (f_past_valid) c_wait3: cover (f_wait == 3);
`endif
endmodule
