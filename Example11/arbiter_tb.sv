// File        :arbiter_tb.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :arbiter_tb
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :Testbench verifies that the arbiter grants only one request at a time using assertions.

module tb;

  logic clk = 0, rst;
  logic [3:0] req;
  logic [3:0] gnt;

  // Clock generation
  always #5 clk = ~clk;

  // DUT
  arbiter dut (
    .clk(clk),
    .rst(rst),
    .req(req),
    .gnt(gnt)
  );

  // Assertion: only one or zero grant active
  assert property (@(posedge clk) $onehot0(gnt))
    else $error("Protocol Violation: Multiple Grants!");

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    rst = 1;
    req = 0;
    #10 rst = 0;

    repeat (10) begin
      req = $urandom_range(0,15); // random requests
      @(posedge clk);
    end

    $finish;
  end

endmodule
