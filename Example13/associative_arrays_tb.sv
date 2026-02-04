// File        :associate_arrays_tb.sv
// Author      :Sanica M S /1BM23EC229
// Created     :04-02-2026
// Module      :memory_model_tb
// Project     :SystemVerilog & Verification(23EC6PE2SV)
// Faculty     :Prof.Ajaykumar Devarapalli
// Description :Associative array memory stores data only for used addresses, efficiently modeling large memories.

module tb;

  logic clk = 0;
  logic wr_en, rd_en;
  int addr;
  int wdata;
  int rdata;

  // Clock generation
  always #5 clk = ~clk;

  // DUT
  memory_model dut (
    .clk(clk),
    .wr_en(wr_en),
    .rd_en(rd_en),
    .addr(addr),
    .wdata(wdata),
    .rdata(rdata)
  );

  initial begin
    $dumpfile("dump.vcd");
    $dumpvars;
    wr_en = 0;
    rd_en = 0;
    addr  = 0;
    wdata = 0;

    // Write random data
    repeat (5) begin
      @(posedge clk);
      wr_en = 1;
      addr  = $urandom_range(0,100);
      wdata = $urandom_range(0,255);
      $display("WRITE: addr=%0d data=%0d", addr, wdata);
    end

    @(posedge clk);
    wr_en = 0;

    // Read random addresses
    repeat (5) begin
      @(posedge clk);
      rd_en = 1;
      addr  = $urandom_range(0,100);
      @(posedge clk);
      $display("READ: addr=%0d data=%0d", addr, rdata);
    end

    rd_en = 0;

    #10 $finish;
  end

endmodule
