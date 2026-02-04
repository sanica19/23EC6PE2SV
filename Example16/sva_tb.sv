// File        :sva_tb.sv
// Author      :Sanica M S/1BM23EC229
// Created     :04-02-2026
// Module      :sva_tb
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :Concurrent assertion verifies that grant signal occurs exactly two clock cycles after a request.
module tb;

  bit clk = 0, req = 0, gnt = 0;

  // Clock generation
  always #5 clk = ~clk;

  // Property: grant must come 2 cycles after request
  property p_handshake;
    @(posedge clk) req |=> ##2 gnt;
  endproperty

  // Assertion
  assert property (p_handshake)
    else $error("Protocol Fail!");

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    // Generate request
    @(posedge clk) req <= 1;
    @(posedge clk) req <= 0;

    // Grant after 2 cycles → assertion passes
    @(posedge clk);
    @(posedge clk) gnt <= 1;

    #50 $finish;
  end

endmodule
